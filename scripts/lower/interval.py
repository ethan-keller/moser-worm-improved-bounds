"""Exact generator-side copy of Common.Interval.Basic (scale 2^-56)."""

from dataclasses import dataclass
from math import isqrt

SCALE = 56
ONE = 1 << SCALE
PI_LO = 226375608064910088
PI2_LO = 113187804032455044
PI4_LO = 56593902016227522
SIN_COEFFS = (
    12009599006321322,
    600479950316066,
    14297141674192,
    198571412141,
    1805194655,
    11571760,
    55103,
    202,
)
COS_COEFFS = (
    36028797018963968,
    3002399751580330,
    100079991719344,
    1787142709274,
    19857141214,
    150432887,
    826554,
    3443,
    11,
)


@dataclass(frozen=True)
class Interval:
    __slots__ = ("lo", "hi")
    lo: int
    hi: int

    @classmethod
    def point(cls, mantissa):
        return cls(mantissa, mantissa)

    @classmethod
    def ratio(cls, numerator, denominator=1):
        if denominator <= 0:
            raise ValueError("positive denominator required")
        n = numerator * ONE
        return cls(n // denominator, -((-n) // denominator))

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __sub__(self, other):
        return Interval(self.lo - other.hi, self.hi - other.lo)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __mul__(self, other):
        products = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return Interval(min(products) // ONE, -((-max(products)) // ONE))

    def half(self):
        return Interval(self.lo // 2, -((-self.hi) // 2))

    def absolute(self):
        if self.lo >= 0:
            return self
        if self.hi <= 0:
            return -self
        return Interval(0, max(-self.lo, self.hi))

    def square(self):
        a = self.absolute()
        return Interval(a.lo * a.lo // ONE, -((-a.hi * a.hi) // ONE))

    def sqrt(self):
        lo, hi = max(0, self.lo) * ONE, max(0, self.hi) * ONE
        lroot, hroot = isqrt(lo), isqrt(hi)
        return Interval(lroot, hroot + (hroot * hroot != hi))

    def clamp_unit(self):
        return Interval(max(self.lo, -ONE), min(self.hi, ONE))

    def midpoint(self):
        return self.lo + (self.hi - self.lo) // 2

    def radius(self):
        mid = self.midpoint()
        return max(self.hi - mid, mid - self.lo)

    def magnitude(self):
        return max(abs(self.lo), abs(self.hi))


ZERO = Interval.point(0)
UNIT = Interval.point(ONE)
PI = Interval(PI_LO, PI_LO + 1)


def horner(x, coefficients):
    result = Interval(coefficients[-1], coefficients[-1] + 1)
    for coefficient in reversed(coefficients[:-1]):
        result = Interval(coefficient, coefficient + 1) - x * result
    return result


def sincos_point(t):
    if abs(t) > 64 * ONE:
        raise ValueError("angle outside the proved range")
    k = (t + PI4_LO) // PI2_LO
    for _ in range(8):
        residual = Interval.point(t) - Interval.ratio(k) * Interval(PI2_LO, PI2_LO + 1)
        if residual.hi > PI4_LO + 64:
            k += 1
        elif residual.lo < -PI4_LO - 64:
            k -= 1
        else:
            break
    residual = Interval.point(t) - Interval.ratio(k) * Interval(PI2_LO, PI2_LO + 1)
    square = residual.square()
    sine = residual * (UNIT - square * horner(square, SIN_COEFFS))
    cosine = UNIT - square * horner(square, COS_COEFFS)
    sine = Interval(sine.lo - 1, sine.hi + 1)
    cosine = Interval(cosine.lo - 1, cosine.hi + 1)
    sine, cosine = ((sine, cosine), (cosine, -sine), (-sine, -cosine), (-cosine, sine))[k % 4]
    return sine.clamp_unit(), cosine.clamp_unit()


def sincos(interval):
    mid, radius = interval.midpoint(), interval.radius()
    sine, cosine = sincos_point(mid)
    return (
        Interval(sine.lo - radius, sine.hi + radius).clamp_unit(),
        Interval(cosine.lo - radius, cosine.hi + radius).clamp_unit(),
    )
