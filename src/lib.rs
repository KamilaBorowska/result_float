//! This crate contains floating point types that error if they are set to NaN.
//!
//! # Examples
//!
//! ```
//! # fn main() -> Result<(), result_float::NaN> {
//! use result_float::{rf, Rf64, Result};
//!
//! fn geometric_mean(a: Rf64, b: Rf64) -> Result<f64> {
//!     (a * b)?.sqrt()
//! }
//!
//! fn mean(a: Rf64, b: Rf64) -> Result<f64> {
//!     (a + b)? * rf(0.5)?
//! }
//!
//! println!("geometric_mean(10.0, 20.0) = {}", geometric_mean(rf(10.0)?, rf(20.0)?)?);
//! //prints 14.142...
//! assert!(mean(rf(10.0)?, rf(20.0)?)? == rf(15.0)?);
//! # Ok(())
//! # }
//! ```
#![no_std]
#![deny(missing_docs)]

#[cfg(test)]
#[macro_use]
extern crate std;
extern crate failure;
#[macro_use]
extern crate failure_derive;
extern crate num_traits;
#[cfg(feature = "serde")]
extern crate serde;
#[cfg(test)]
#[macro_use]
extern crate quickcheck;

// failure_derive may be used with std feature, causing issues
#[allow(unused_imports)]
#[cfg(not(test))]
use core as std;

use core::cmp::Ordering;
use core::fmt::{self, Display, Formatter, LowerExp, UpperExp};
use core::hash::{Hash, Hasher};
use core::num::FpCategory;
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use num_traits::float::FloatCore;
#[cfg(feature = "std")]
use num_traits::Float;
#[cfg(feature = "serde")]
use serde::de::{Deserialize, Deserializer, Error};
#[cfg(feature = "serde")]
use serde::ser::{Serialize, Serializer};

/// An error which is returned when an operation returns NaN.
///
/// ```
/// use std::f64::NAN;
/// use result_float::{rf, NaN};
/// assert_eq!(rf(NAN), Err(NaN));
/// ```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Fail)]
#[fail(display = "NaN")]
pub struct NaN;

/// A floating point number that cannot store NaN.
///
/// Usually there is no need to access this struct directly, and instead
/// one of aliases like [`Rf32`] or [`Rf64`] could be used instead.
///
/// [Rf32]: ./type.Rf32.html
/// [Rf64]: ./type.Rf64.html
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ResultFloat<F>(F);

impl<F> Eq for ResultFloat<F> where F: PartialEq {}

impl<F> PartialOrd for ResultFloat<F>
where
    F: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<F> Ord for ResultFloat<F>
where
    F: PartialOrd,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// The type returned by most [`ResultFloat`] operations.
///
/// [ResultFloat]: struct.ResultFloat.html
pub type Result<F> = core::result::Result<ResultFloat<F>, NaN>;

/// A floating point number behaving like `f32` that does not allow NaN.
pub type Rf32 = ResultFloat<f32>;
/// A floating point number behaving like `f64` that does not allow NaN.
pub type Rf64 = ResultFloat<f64>;

fn rfu<F>(f: F) -> ResultFloat<F>
where
    F: FloatCore,
{
    rf(f).unwrap()
}

impl<F> ResultFloat<F>
where
    F: FloatCore,
{
    /// Constructs a `ResultFloat` with the given value.
    ///
    /// Returns `Err` if the value is `NaN`.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::{rf, ResultFloat};
    ///
    /// assert_eq!(ResultFloat::new(1.0)?, rf(1.0)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn new(v: F) -> Result<F> {
        if v.is_nan() {
            Err(NaN)
        } else {
            Ok(ResultFloat(v))
        }
    }

    /// Returns the underlying float value.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// assert_eq!(rf(3.14)?.raw(), 3.14);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn raw(self) -> F {
        self.0
    }

    /// Returns `true` if this value is positive infinity or negative infinity and
    /// false otherwise.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let f = rf(7.0)?;
    /// let inf = rf(f64::INFINITY)?;
    /// let neg_inf = rf(f64::NEG_INFINITY)?;
    ///
    /// assert!(!f.is_infinite());
    /// assert!(inf.is_infinite());
    /// assert!(neg_inf.is_infinite());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    /// Returns `true` if this number is not infinite.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let f = rf(7.0f64)?;
    /// let inf = rf(f64::INFINITY)?;
    /// let neg_inf = rf(f64::NEG_INFINITY)?;
    ///
    /// assert!(f.is_finite());
    /// assert!(!inf.is_finite());
    /// assert!(!neg_inf.is_finite());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn is_finite(self) -> bool {
        self.0.is_finite()
    }

    /// Returns `true` if the number is neither zero, infinite,
    /// or [subnormal][subnormal].
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let min = rf(f64::MIN_POSITIVE)?; // 2.2250738585072014e-308f64
    /// let max = rf(f64::MAX)?;
    /// let lower_than_min = rf(1.0e-308_f64)?;
    /// let zero = rf(0.0f64)?;
    ///
    /// assert!(min.is_normal());
    /// assert!(max.is_normal());
    ///
    /// assert!(!zero.is_normal());
    /// assert!(!rf(f64::INFINITY)?.is_normal());
    /// // Values between `0` and `min` are Subnormal.
    /// assert!(!lower_than_min.is_normal());
    /// # Ok(())
    /// # }
    /// ```
    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
    #[inline]
    pub fn is_normal(self) -> bool {
        self.0.is_normal()
    }

    /// Returns the floating point category of the number. If only one property
    /// is going to be tested, it is generally faster to use the specific
    /// predicate instead.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::num::FpCategory;
    /// use std::f64;
    ///
    /// let num = rf(12.4)?;
    /// let inf = rf(f64::INFINITY)?;
    ///
    /// assert_eq!(num.classify(), FpCategory::Normal);
    /// assert_eq!(inf.classify(), FpCategory::Infinite);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn classify(self) -> FpCategory {
        self.0.classify()
    }

    /// Returns the largest integer less than or equal to a number.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(3.99)?;
    /// let g = rf(3.0)?;
    ///
    /// assert_eq!(f.floor(), rf(3.0)?);
    /// assert_eq!(g.floor(), rf(3.0)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn floor(self) -> Self {
        rfu(self.0.floor())
    }

    /// Returns the smallest integer greater than or equal to a number.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(3.01)?;
    /// let g = rf(4.0)?;
    ///
    /// assert_eq!(f.ceil(), rf(4.0)?);
    /// assert_eq!(g.ceil(), rf(4.0)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn ceil(self) -> Self {
        rfu(self.0.ceil())
    }

    /// Returns the nearest integer to a number. Round half-way cases away from
    /// `0.0`.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(3.3)?;
    /// let g = rf(-3.3)?;
    ///
    /// assert_eq!(f.round(), rf(3.0)?);
    /// assert_eq!(g.round(), rf(-3.0)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn round(self) -> Self {
        rfu(self.0.round())
    }

    /// Returns the integer part of a number.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(3.3)?;
    /// let g = rf(-3.7)?;
    ///
    /// assert_eq!(f.trunc(), rf(3.0)?);
    /// assert_eq!(g.trunc(), rf(-3.0)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn trunc(self) -> Self {
        rfu(self.0.trunc())
    }

    /// Returns the fractional part of a number.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(3.5)?;
    /// let y = rf(-3.5)?;
    /// let abs_difference_x = (x.fract()? - rf(0.5)?)?.abs();
    /// let abs_difference_y = (y.fract()? - rf(-0.5)?)?.abs();
    ///
    /// assert!(abs_difference_x < rf(1e-10)?);
    /// assert!(abs_difference_y < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn fract(self) -> Result<F> {
        rf(self.0.fract())
    }

    /// Computes the absolute value of `self`.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let x = rf(3.5)?;
    /// let y = rf(-3.5)?;
    ///
    /// let abs_difference_x = (x.abs() - x)?.abs();
    /// let abs_difference_y = (y.abs() - (-y))?.abs();
    ///
    /// assert!(abs_difference_x < rf(1e-10)?);
    /// assert!(abs_difference_y < rf(1e-10)?);
    ///
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn abs(self) -> Self {
        rfu(self.0.abs())
    }

    /// Returns a number that represents the sign of `self`.
    ///
    /// - `1.0` if the number is positive, `+0.0` or `INFINITY`
    /// - `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let f = rf(3.5)?;
    ///
    /// assert_eq!(f.signum(), rf(1.0)?);
    /// assert_eq!(rf(f64::NEG_INFINITY)?.signum(), rf(-1.0)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn signum(self) -> Self {
        rfu(self.0.signum())
    }

    /// Returns `true` if and only if `self` has a positive sign, including `+0.0`
    /// and positive infinity.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// let f = rf(7.0)?;
    /// let g = rf(-7.0)?;
    ///
    /// assert!(f.is_sign_positive());
    /// assert!(!g.is_sign_positive());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn is_sign_positive(self) -> bool {
        self.0.is_sign_positive()
    }

    /// Returns `true` if and only if `self` has a negative sign, including `-0.0`
    /// and negative infinity.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(7.0)?;
    /// let g = rf(-7.0)?;
    ///
    /// assert!(!f.is_sign_negative());
    /// assert!(g.is_sign_negative());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn is_sign_negative(self) -> bool {
        self.0.is_sign_negative()
    }

    /// Takes the reciprocal (inverse) of a number, `1/x`.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(2.0)?;
    /// let abs_difference = (x.recip() - (rf(1.0)?/x)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn recip(self) -> Self {
        rfu(self.0.recip())
    }

    /// Raises a number to an integer power.
    ///
    /// Using this function is generally faster than using `powf`. Additionally,
    /// this function cannot return an error value.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(2.0)?;
    /// let abs_difference = (x.powi(2) - (x*x)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn powi(self, n: i32) -> Self {
        rfu(self.0.powi(n))
    }

    /// Converts degrees to radians.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64::consts::PI;
    ///
    /// let angle = rf(180.0)?;
    ///
    /// let abs_difference = (angle.to_radians()? - rf(PI)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn to_degrees(self) -> Result<F> {
        rf(self.0.to_degrees())
    }

    /// Converts degrees to radians.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64::consts::PI;
    ///
    /// let angle = rf(180.0)?;
    ///
    /// let abs_difference = (angle.to_radians()? - rf(PI)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn to_radians(self) -> Result<F> {
        rf(self.0.to_radians())
    }
}

#[cfg(feature = "std")]
impl<F> ResultFloat<F>
where
    F: FloatCore + Float,
{
    /// Fused multiply-add. Computes `(self * a) + b` with only one rounding
    /// error. This produces a more accurate result with better performance than
    /// a separate multiplication operation followed by an add.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let m = rf(10.0)?;
    /// let x = rf(4.0)?;
    /// let b = rf(60.0)?;
    ///
    /// // 100.0
    /// let abs_difference = (m.mul_add(x, b)? - ((m*x)? + b)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn mul_add(self, a: Self, b: Self) -> Result<F> {
        rf(self.0.mul_add(a.0, b.0))
    }

    /// Raises a number to a floating point power.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(2.0)?;
    /// let abs_difference = (x.powf(rf(2.0)?)? - (x*x)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn powf(self, n: Self) -> Result<F> {
        rf(self.0.powf(n.0))
    }

    /// Takes the square root of a number.
    ///
    /// Returns NaN if `self` is a negative number.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let positive = rf(4.0)?;
    /// let negative = rf(-4.0)?;
    ///
    /// let abs_difference = (positive.sqrt()? - rf(2.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// assert!(negative.sqrt().is_err());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn sqrt(self) -> Result<F> {
        rf(self.0.sqrt())
    }

    /// Returns `e^(self)`, (the exponential function).
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let one = rf(1.0)?;
    /// // e^1
    /// let e = one.exp();
    ///
    /// // ln(e) - 1 == 0
    /// let abs_difference = (e.ln()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn exp(self) -> Self {
        rfu(self.0.exp())
    }

    /// Returns `2^(self)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(2.0)?;
    ///
    /// // 2^2 - 4 == 0
    /// let abs_difference = (f.exp2() - rf(4.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn exp2(self) -> Self {
        rfu(self.0.exp2())
    }

    /// Returns the natural logarithm of the number.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let one = rf(1.0)?;
    /// // e^1
    /// let e = one.exp();
    ///
    /// // ln(e) - 1 == 0
    /// let abs_difference = (e.ln()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn ln(self) -> Result<F> {
        rf(self.0.ln())
    }

    /// Returns the logarithm of the number with respect to an arbitrary base.
    ///
    /// The result may not be correctly rounded owing to implementation details;
    /// `self.log2()` can produce more accurate results for base 2, and
    /// `self.log10()` can produce more accurate results for base 10.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let five = rf(5.0)?;
    ///
    /// // log5(5) - 1 == 0
    /// let abs_difference = (five.log(rf(5.0)?)? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn log(self, base: Self) -> Result<F> {
        rf(self.0.log(base.0))
    }

    /// Returns the base 2 logarithm of the number.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let two = rf(2.0)?;
    ///
    /// // log2(2) - 1 == 0
    /// let abs_difference = (two.log2()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn log2(self) -> Result<F> {
        rf(self.0.log2())
    }

    /// Returns the base 10 logarithm of the number.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let ten = rf(10.0)?;
    ///
    /// // log10(10) - 1 == 0
    /// let abs_difference = (ten.log10()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn log10(self) -> Result<F> {
        rf(self.0.log10())
    }

    /// Takes the cubic root of a number.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(8.0)?;
    ///
    /// // x^(1/3) - 2 == 0
    /// let abs_difference = (x.cbrt() - rf(2.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn cbrt(self) -> Self {
        rfu(self.0.cbrt())
    }

    /// Calculates the length of the hypotenuse of a right-angle triangle given
    /// legs of length `x` and `y`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(2.0)?;
    /// let y = rf(3.0)?;
    ///
    /// // sqrt(x^2 + y^2)
    /// let abs_difference = (x.hypot(y) - (x.powi(2) + y.powi(2))?.sqrt()?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn hypot(self, other: Self) -> Self {
        rfu(self.0.hypot(other.0))
    }

    /// Computes the sine of a number (in radians).
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let x = (rf(f64::consts::PI)? / rf(2.0)?)?;
    ///
    /// let abs_difference = (x.sin()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn sin(self) -> Result<F> {
        rf(self.0.sin())
    }

    /// Computes the cosine of a number (in radians).
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let x = (rf(2.0)? * rf(f64::consts::PI)?)?;
    ///
    /// let abs_difference = (x.cos()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn cos(self) -> Result<F> {
        rf(self.0.cos())
    }

    /// Computes the tangent of a number (in radians).
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let x = (rf(f64::consts::PI)? / rf(4.0)?)?;
    /// let abs_difference = (x.tan()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-14)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn tan(self) -> Result<F> {
        rf(self.0.tan())
    }

    /// Computes the arcsine of a number. Return value is in radians in
    /// the range [-pi/2, pi/2] or NaN if the number is outside the range
    /// [-1, 1].
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let f = (rf(f64::consts::PI)? / rf(2.0)?)?;
    ///
    /// // asin(sin(pi/2))
    /// let abs_difference = (f.sin()?.asin()? - (rf(f64::consts::PI)? / rf(2.0)?)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn asin(self) -> Result<F> {
        rf(self.0.asin())
    }

    /// Computes the arccosine of a number. Return value is in radians in
    /// the range [0, pi] or NaN if the number is outside the range
    /// [-1, 1].
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let f = (rf(f64::consts::PI)? / rf(4.0)?)?;
    ///
    /// // acos(cos(pi/4))
    /// let abs_difference = (f.cos()?.acos()? - (rf(f64::consts::PI)? / rf(4.0)?)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn acos(self) -> Result<F> {
        rf(self.0.acos())
    }

    /// Computes the arctangent of a number. Return value is in radians in the
    /// range [-pi/2, pi/2];
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let f = rf(1.0)?;
    ///
    /// // atan(tan(1))
    /// let abs_difference = (f.tan()?.atan() - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn atan(self) -> Self {
        rfu(self.0.atan())
    }

    /// Computes the four quadrant arctangent of `self` (`y`) and `other` (`x`) in radians.
    ///
    /// * `x = 0`, `y = 0`: `0`
    /// * `x >= 0`: `arctan(y/x)` -> `[-pi/2, pi/2]`
    /// * `y >= 0`: `arctan(y/x) + pi` -> `(pi/2, pi]`
    /// * `y < 0`: `arctan(y/x) - pi` -> `(-pi, -pi/2)`
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let pi = rf(f64::consts::PI)?;
    /// // Positive angles measured counter-clockwise
    /// // from positive x axis
    /// // -pi/4 radians (45 deg clockwise)
    /// let x1 = rf(3.0)?;
    /// let y1 = -rf(3.0)?;
    ///
    /// // 3pi/4 radians (135 deg counter-clockwise)
    /// let x2 = -rf(3.0)?;
    /// let y2 = rf(3.0)?;
    ///
    /// let abs_difference_1 = (y1.atan2(x1) - (-pi/rf(4.0)?)?)?.abs();
    /// let abs_difference_2 = (y2.atan2(x2) - ((rf(3.0)?*pi)?/rf(4.0)?)?)?.abs();
    ///
    /// assert!(abs_difference_1 < rf(1e-10)?);
    /// assert!(abs_difference_2 < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn atan2(self, other: Self) -> Self {
        rfu(self.0.atan2(other.0))
    }

    /// Simultaneously computes the sine and cosine of the number, `x`. Returns
    /// `(sin(x), cos(x))`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let x = (rf(f64::consts::PI)?/rf(4.0)?)?;
    /// let f = x.sin_cos()?;
    ///
    /// let abs_difference_0 = (f.0 - x.sin()?)?.abs();
    /// let abs_difference_1 = (f.1 - x.cos()?)?.abs();
    ///
    /// assert!(abs_difference_0 < rf(1e-10)?);
    /// assert!(abs_difference_1 < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn sin_cos(self) -> core::result::Result<(Self, Self), NaN> {
        let (a, b) = self.0.sin_cos();
        Ok((rf(a)?, rf(b)?))
    }

    /// Returns `e^(self) - 1` in a way that is accurate even if the
    /// number is close to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(7.0)?;
    ///
    /// // e^(ln(7)) - 1
    /// let abs_difference = (x.ln()?.exp_m1() - rf(6.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn exp_m1(self) -> Self {
        rfu(self.0.exp_m1())
    }

    /// Returns `ln(1+n)` (natural logarithm) more accurately than if
    /// the operations were performed separately.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let x = (rf(f64::consts::E)? - rf(1.0)?)?;
    ///
    /// // ln(1 + (e - 1)) == ln(e) == 1
    /// let abs_difference = (x.ln_1p()? - rf(1.0)?)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn ln_1p(self) -> Result<F> {
        rf(self.0.ln_1p())
    }

    /// Hyperbolic sine function.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let e = rf(f64::consts::E)?;
    /// let x = rf(1.0)?;
    ///
    /// let f = x.sinh();
    /// // Solving sinh() at 1 gives `(e^2-1)/(2e)`
    /// let g = ((e.powi(2) - rf(1.0)?)?/(rf(2.0)?*e)?)?;
    /// let abs_difference = (f - g)?.abs();
    ///
    /// assert!(abs_difference < rf(1e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn sinh(self) -> Self {
        rfu(self.0.sinh())
    }

    /// Hyperbolic cosine function.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let e = rf(f64::consts::E)?;
    /// let x = rf(1.0)?;
    /// let f = x.cosh();
    /// // Solving cosh() at 1 gives this result
    /// let g = ((e.powi(2) + rf(1.0)?)?/(rf(2.0)?*e)?)?;
    /// let abs_difference = (f - g)?.abs();
    ///
    /// // Same result
    /// assert!(abs_difference < rf(1.0e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn cosh(self) -> Self {
        rfu(self.0.cosh())
    }

    /// Hyperbolic tangent function.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let e = rf(f64::consts::E)?;
    /// let x = rf(1.0)?;
    ///
    /// let f = x.tanh();
    /// // Solving tanh() at 1 gives `(1 - e^(-2))/(1 + e^(-2))`
    /// let g = ((rf(1.0)? - e.powi(-2))?/(rf(1.0)? + e.powi(-2))?)?;
    /// let abs_difference = (f - g)?.abs();
    ///
    /// assert!(abs_difference < rf(1.0e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn tanh(self) -> Self {
        rfu(self.0.tanh())
    }

    /// Inverse hyperbolic sine function.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(1.0)?;
    /// let f = x.sinh().asinh();
    ///
    /// let abs_difference = (f - x)?.abs();
    ///
    /// assert!(abs_difference < rf(1.0e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn asinh(self) -> Self {
        rfu(self.0.asinh())
    }

    /// Inverse hyperbolic cosine function.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    ///
    /// let x = rf(1.0)?;
    /// let f = x.cosh().acosh()?;
    ///
    /// let abs_difference = (f - x)?.abs();
    ///
    /// assert!(abs_difference < rf(1.0e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn acosh(self) -> Result<F> {
        rf(self.0.acosh())
    }

    /// Inverse hyperbolic tangent function.
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// use std::f64;
    ///
    /// let e = rf(f64::consts::E)?;
    /// let f = e.tanh().atanh()?;
    ///
    /// let abs_difference = (f - e)?.abs();
    ///
    /// assert!(abs_difference < rf(1.0e-10)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn atanh(self) -> Result<F> {
        rf(self.0.atanh())
    }
}

impl ResultFloat<f32> {
    /// Raw transmutation to `u32`.
    ///
    /// This is currently identical to `transmute::<f32, u32>(self.raw())` on all platforms.
    ///
    /// Note that this function is distinct from `as` casting, which attempts to
    /// preserve the *numeric* value, and not the bitwise value.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// assert!(rf(1f32)?.to_bits() != 1f32 as u32); // to_bits() is not casting!
    /// assert_eq!(rf(12.5f32)?.to_bits(), 0x41480000);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    /// Raw transmutation from `u32`.
    ///
    /// This is currently identical to `rf(transmute::<u32, f32>(v))` on all platforms.
    /// It turns out this is incredibly portable, for two reasons:
    ///
    /// * Floats and Ints have the same endianness on all supported platforms.
    /// * IEEE-754 very precisely specifies the bit layout of floats.
    ///
    /// Note that this function is distinct from `as` casting, which attempts to
    /// preserve the *numeric* value, and not the bitwise value.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::{rf, Rf32};
    /// let v = Rf32::from_bits(0x41480000)?;
    /// let difference = (v - rf(12.5)?)?.abs();
    /// assert!(difference <= rf(1e-5)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn from_bits(v: u32) -> Result<f32> {
        rf(f32::from_bits(v))
    }
}

impl ResultFloat<f64> {
    /// Raw transmutation to `u64`.
    ///
    /// This is currently identical to `transmute::<f64, u64>(self.raw())` on all platforms.
    ///
    /// Note that this function is distinct from `as` casting, which attempts to
    /// preserve the *numeric* value, and not the bitwise value.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::rf;
    /// assert!(rf(1f64)?.to_bits() != 1f64 as u64); // to_bits() is not casting!
    /// assert_eq!(rf(12.5f64)?.to_bits(), 0x4029000000000000);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn to_bits(self) -> u64 {
        self.0.to_bits()
    }

    /// Raw transmutation from `u64`.
    ///
    /// This is currently identical to `rf(transmute::<u64, f64>(v))` on all platforms.
    /// It turns out this is incredibly portable, for two reasons:
    ///
    /// * Floats and Ints have the same endianness on all supported platforms.
    /// * IEEE-754 very precisely specifies the bit layout of floats.
    ///
    /// Note that this function is distinct from `as` casting, which attempts to
    /// preserve the *numeric* value, and not the bitwise value.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), result_float::NaN> {
    /// use result_float::{rf, Rf64};
    /// let v = Rf64::from_bits(0x4029000000000000)?;
    /// let difference = (v - rf(12.5)?)?.abs();
    /// assert!(difference <= rf(1e-5)?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn from_bits(v: u64) -> Result<f64> {
        rf(f64::from_bits(v))
    }
}

macro_rules! op_impl {
    ($( $imp:ident $method:ident $op:tt ) *) => {
        $(
            impl<F> $imp for ResultFloat<F>
            where
                F: FloatCore
            {
                type Output = Result<F>;
                #[inline]
                fn $method(self, other: Self) -> Result<F> {
                    rf(self.0 $op other.0)
                }
            }
        )*
    };
}

op_impl!(
    Add add +
    Sub sub -
    Mul mul *
    Div div /
    Rem rem %
);

impl<F> Neg for ResultFloat<F>
where
    F: FloatCore,
{
    type Output = ResultFloat<F>;
    #[inline]
    fn neg(self) -> ResultFloat<F> {
        rfu(-self.0)
    }
}

macro_rules! format_impl {
    ($($imp:ident)*) => {
        $(
            impl<F> $imp for ResultFloat<F>
            where
                F: $imp,
            {
                #[inline]
                fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                    self.0.fmt(f)
                }
            }
        )*
    };
}

format_impl!(Display LowerExp UpperExp);

macro_rules! hash {
    ($($t:ident $method:ident)*) => {
        $(
            impl Hash for ResultFloat<$t> {
                fn hash<H>(&self, state: &mut H)
                where
                    H: Hasher,
                {
                    state.$method(if self.0 == 0.0 { 0 } else { self.0.to_bits() })
                }
            }
        )*
    };
}

hash!(f32 write_u32 f64 write_u64);

impl<F> Default for ResultFloat<F>
where
    F: Default + FloatCore,
{
    fn default() -> ResultFloat<F> {
        rf(F::default()).unwrap()
    }
}

#[cfg(feature = "serde")]
/// Requires crate feature `serde`
impl<F> Serialize for ResultFloat<F>
where
    F: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> core::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
/// Requires crate feature `serde`
impl<'de, F> Deserialize<'de> for ResultFloat<F>
where
    F: Deserialize<'de> + FloatCore,
{
    fn deserialize<D>(deserializer: D) -> core::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        rf(F::deserialize(deserializer)?).map_err(D::Error::custom)
    }
}

/// Shorthand for [`ResultFloat::new(value)`].
///
/// ```
/// # fn main() -> Result<(), result_float::NaN> {
/// use result_float::rf;
/// assert_eq!((rf(0.5)? * rf(2.0)?)?, rf(1.0)?);
/// # Ok(())
/// # }
/// ```
///
/// [`ResultFloat::new(value)`]: ./struct.ResultFloat.html#method.new
#[inline]
pub fn rf<F>(v: F) -> Result<F>
where
    F: FloatCore,
{
    ResultFloat::new(v)
}

#[cfg(test)]
mod tests {
    use crate::{rf, Rf64};
    use core::hash::{Hash, Hasher};
    use quickcheck::TestResult;

    struct TestHasher {
        value: u64,
        shift: u8,
    }

    impl Hasher for TestHasher {
        fn finish(&self) -> u64 {
            self.value
        }

        fn write(&mut self, bytes: &[u8]) {
            for &b in bytes {
                self.value += u64::from(b) << self.shift;
                self.shift += 8;
            }
        }
    }

    fn hash(v: impl Hash) -> u64 {
        let mut hasher = TestHasher { value: 0, shift: 0 };
        v.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn test_positive_zero_f32() {
        assert_eq!(hash(rf(0.0f32).unwrap()), 0);
    }

    #[test]
    fn test_negative_zero_f32() {
        assert_eq!(hash(rf(-0.0f32).unwrap()), 0);
    }

    #[test]
    fn test_positive_zero_f64() {
        assert_eq!(hash(rf(0.0).unwrap()), 0);
    }

    #[test]
    fn test_negative_zero_f64() {
        assert_eq!(hash(rf(-0.0).unwrap()), 0);
    }

    macro_rules! rf {
        ($x:expr) => {{
            let x = $x;
            if x.is_nan() {
                return TestResult::discard();
            }
            rf(x).unwrap()
        }};
    }

    quickcheck! {
        fn floor(x: f64) -> TestResult {
            TestResult::from_bool(rf!(x).floor().raw() == x.floor())
        }

        fn acosh(x: f64) -> TestResult {
            let x = rf!(x).abs();
            TestResult::from_bool((x.cosh().acosh().unwrap() - x).unwrap() < rf(1e-10).unwrap())
        }

        fn hash_f32(x: f32) -> TestResult {
            let x = rf!(x);
            if x == rf!(0.0f32) && x.is_sign_negative() {
                TestResult::discard()
            } else {
                TestResult::from_bool(hash(x) == x.to_bits().into())
            }
        }

        fn hash_f64(x: f64) -> TestResult {
            let x = rf!(x);
            if x == rf!(0.0f64) && x.is_sign_negative() {
                TestResult::discard()
            } else {
                TestResult::from_bool(hash(x) == x.to_bits())
            }
        }
    }

    #[test]
    fn test_default() {
        assert_eq!(Rf64::default(), rf(0.0).unwrap());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_ser_de() {
        extern crate serde_test;
        serde_test::assert_tokens(&rf(3.14).unwrap(), &[serde_test::Token::F64(3.14)]);
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", rf(3.14).unwrap()), "3.14");
    }
}
