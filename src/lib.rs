#![no_std]

#[macro_use]
extern crate failure;
extern crate num_traits;
#[cfg(test)]
#[macro_use]
extern crate quickcheck;

// Fail derive assumes that std is being used
use core as std;

use core::cmp::Ordering;
use core::fmt::{self, Display, Formatter, LowerExp, UpperExp};
use core::hash::{Hash, Hasher};
use core::num::FpCategory;
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use num_traits::float::FloatCore;
#[cfg(feature = "std")]
use num_traits::Float;

#[derive(Copy, Clone, Debug, Fail)]
#[fail(display = "NaN")]
pub struct NaN;

/// A floating point number that cannot store NaN.
///
/// Usually there is no need to access this struct directly, and instead
/// one of aliases like [`Rf32`] or [`Rf64`] could be used instead.
///
/// [Rf32]: ./type.Rf32.html
/// [Rf64]: ./type.Rf64.html
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
pub struct ResultFloat<F>(F);

impl<F> Eq for ResultFloat<F>
where
    F: PartialEq,
{
}

impl<F> Ord for ResultFloat<F>
where
    F: PartialOrd,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

pub type Result<F> = core::result::Result<ResultFloat<F>, NaN>;

/// A floating point number behaving like `f32` that does not allow NaN.
pub type Rf32 = ResultFloat<f32>;
/// A floating point number behaving like `f64` that does not allow NaN.
pub type Rf64 = ResultFloat<f64>;

fn rn<F>(f: F) -> Result<F>
where
    F: FloatCore,
{
    ResultFloat::new(f)
}

fn rnu<F>(f: F) -> ResultFloat<F>
where
    F: FloatCore,
{
    rn(f).unwrap()
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
        rnu(self.0.floor())
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
        rnu(self.0.ceil())
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
        rnu(self.0.round())
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
        rnu(self.0.trunc())
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
        rn(self.0.fract())
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
        rnu(self.0.abs())
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
        rnu(self.0.signum())
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

    #[inline]
    pub fn recip(self) -> Self {
        rnu(self.0.recip())
    }

    #[inline]
    pub fn powi(self, n: i32) -> Self {
        rnu(self.0.powi(n))
    }

    #[inline]
    pub fn to_degrees(self) -> Result<F> {
        rn(self.0.to_degrees())
    }

    #[inline]
    pub fn to_radians(self) -> Result<F> {
        rn(self.0.to_radians())
    }

    #[inline]
    pub fn max(self, other: Self) -> Self {
        rnu(self.0.max(other.0))
    }

    #[inline]
    pub fn min(self, other: Self) -> Self {
        rnu(self.0.min(other.0))
    }
}

#[cfg(feature = "std")]
impl<F> ResultFloat<F>
where
    F: FloatCore + Float,
{
    #[inline]
    pub fn mul_add(self, a: Self, b: Self) -> Result<F> {
        rn(self.0.mul_add(a.0, b.0))
    }

    #[inline]
    pub fn powf(self, n: Self) -> Result<F> {
        rn(self.0.powf(n.0))
    }

    #[inline]
    pub fn sqrt(self) -> Result<F> {
        rn(self.0.sqrt())
    }

    #[inline]
    pub fn exp(self) -> Self {
        rnu(self.0.exp())
    }

    #[inline]
    pub fn exp2(self) -> Self {
        rnu(self.0.exp2())
    }

    #[inline]
    pub fn ln(self) -> Result<F> {
        rn(self.0.ln())
    }

    #[inline]
    pub fn log(self, base: Self) -> Result<F> {
        rn(self.0.log(base.0))
    }

    #[inline]
    pub fn log2(self) -> Result<F> {
        rn(self.0.log2())
    }

    #[inline]
    pub fn log10(self) -> Result<F> {
        rn(self.0.log10())
    }

    #[inline]
    pub fn cbrt(self) -> Self {
        rnu(self.0.cbrt())
    }

    #[inline]
    pub fn hypot(self, other: Self) -> Self {
        rnu(self.0.hypot(other.0))
    }

    #[inline]
    pub fn sin(self) -> Result<F> {
        rn(self.0.sin())
    }

    #[inline]
    pub fn cos(self) -> Result<F> {
        rn(self.0.cos())
    }

    #[inline]
    pub fn tan(self) -> Result<F> {
        rn(self.0.tan())
    }

    #[inline]
    pub fn asin(self) -> Result<F> {
        rn(self.0.asin())
    }

    #[inline]
    pub fn acos(self) -> Result<F> {
        rn(self.0.acos())
    }

    #[inline]
    pub fn atan(self) -> Self {
        rnu(self.0.atan())
    }

    #[inline]
    pub fn atan2(self, other: Self) -> Self {
        rnu(self.0.atan2(other.0))
    }

    #[inline]
    pub fn sin_cos(self) -> core::result::Result<(Self, Self), NaN> {
        let (a, b) = self.0.sin_cos();
        Ok((rn(a)?, rn(b)?))
    }

    #[inline]
    pub fn exp_m1(self) -> Self {
        rnu(self.0.exp_m1())
    }

    #[inline]
    pub fn ln_1p(self) -> Result<F> {
        rn(self.0.ln_1p())
    }

    #[inline]
    pub fn sinh(self) -> Self {
        rnu(self.0.sinh())
    }

    #[inline]
    pub fn cosh(self) -> Self {
        rnu(self.0.cosh())
    }

    #[inline]
    pub fn tanh(self) -> Self {
        rnu(self.0.tanh())
    }

    #[inline]
    pub fn asinh(self) -> Self {
        rnu(self.0.asinh())
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
        rn(self.0.acosh())
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
        rn(self.0.atanh())
    }
}

impl ResultFloat<f32> {
    #[inline]
    pub fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    #[inline]
    pub fn from_bits(v: u32) -> Result<f32> {
        rf(f32::from_bits(v))
    }
}

impl ResultFloat<f64> {
    #[inline]
    pub fn to_bits(self) -> u64 {
        self.0.to_bits()
    }

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
                    rn(self.0 $op other.0)
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
        rnu(-self.0)
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
    use core::hash::{Hash, Hasher};
    use quickcheck::TestResult;
    use rf;

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
}
