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
use core::num::FpCategory;
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use num_traits::float::FloatCore;
#[cfg(feature = "std")]
use num_traits::Float;

#[derive(Copy, Clone, Debug, Fail)]
#[fail(display = "NaN")]
pub struct NaN;

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

pub type Rf32 = ResultFloat<f32>;
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
    #[inline]
    pub fn new(v: F) -> Result<F> {
        if v.is_nan() {
            Err(NaN)
        } else {
            Ok(ResultFloat(v))
        }
    }

    #[inline]
    pub fn raw(self) -> F {
        self.0
    }

    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite()
    }

    #[inline]
    pub fn is_finite(self) -> bool {
        self.0.is_finite()
    }

    #[inline]
    pub fn is_normal(self) -> bool {
        self.0.is_normal()
    }

    #[inline]
    pub fn classify(self) -> FpCategory {
        self.0.classify()
    }

    #[inline]
    pub fn floor(self) -> Self {
        rnu(self.0.floor())
    }

    #[inline]
    pub fn ceil(self) -> Self {
        rnu(self.0.floor())
    }

    #[inline]
    pub fn round(self) -> Self {
        rnu(self.0.round())
    }

    #[inline]
    pub fn trunc(self) -> Self {
        rnu(self.0.trunc())
    }

    #[inline]
    pub fn fract(self) -> Result<F> {
        rn(self.0.fract())
    }

    #[inline]
    pub fn abs(self) -> Self {
        rnu(self.0.abs())
    }

    #[inline]
    pub fn signum(self) -> Self {
        rnu(self.0.signum())
    }

    #[inline]
    pub fn is_sign_positive(self) -> bool {
        self.0.is_sign_positive()
    }

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

    #[inline]
    pub fn acosh(self) -> Result<F> {
        rn(self.0.acosh())
    }

    #[inline]
    pub fn atanh(self) -> Result<F> {
        rn(self.0.atanh())
    }
}

impl ResultFloat<f32> {
    pub fn to_bits(self) -> u32 {
        self.0.to_bits()
    }

    pub fn from_bits(v: u32) -> Result<f32> {
        rf(f32::from_bits(v))
    }
}

impl ResultFloat<f64> {
    pub fn to_bits(self) -> u64 {
        self.0.to_bits()
    }

    pub fn from_bits(v: u64) -> Result<f64> {
        rf(f64::from_bits(v))
    }
}

macro_rules! op_impl {
    ($imp:ident $method:ident $op:tt) => {
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
    };
}

op_impl!(Add add +);
op_impl!(Sub sub -);
op_impl!(Mul mul *);
op_impl!(Div div /);
op_impl!(Rem rem %);

impl<F> Neg for ResultFloat<F>
where
    F: FloatCore,
{
    type Output = ResultFloat<F>;
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
                fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                    self.0.fmt(f)
                }
            }
        )*
    };
}

format_impl!(Display LowerExp UpperExp);

pub fn rf<F>(v: F) -> Result<F>
where
    F: FloatCore,
{
    ResultFloat::new(v)
}

#[cfg(test)]
mod tests {
    use quickcheck::TestResult;
    use rf;

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
    }
}
