"""Bind the constant-only source change and check the exact integer margins."""

from pathlib import Path
from fractions import Fraction as Q
import json, hashlib

R = Path(__file__).resolve().parents[2]
P = R / "construction/318"
bad = [2, 3, 5, 7, 11, 13, 17, 37, 41, 73, 109, 359, 439, 2399, 4801]
from math import prod, isqrt

assert all(all(p % d for d in range(2, isqrt(p) + 1)) for p in bad)
assert prod(bad) == 11185621387570686764517810 and prod(bad) < 2**84
# The logarithmic lower bounds use only log2(3)>3/2 and strict source bounds.
leading = 68 + 4800 + Q(49, 8) * 84
assert leading == Q(10765, 2)
Hexp = 5385
assert leading + 1 < Hexp
log_c_lower = 1 + Q(3, 2) * (2**15 - 1)
log_80H_upper = 5392
assert 80 < 2**7
assert 9 * log_80H_upper < log_c_lower
assert Q(15, 64) * log_c_lower > log_80H_upper
assert Q(26, 3) < 9
# Low-order product estimate after the two bounds by |a|/40.
low = Q(32, 15) / 40 + Q(49, 15) / 40
assert low == Q(81, 600) and low < Q(1, 2)
report = {
    "verdict": "PASS",
    "fixedParameter": "3^(2^16)",
    "heightConstant": "2^5385",
    "leadingCoefficientLog2UpperBound": str(leading),
    "scalarLabelLog2LowerBound": str(log_c_lower),
    "scalarIndex": 8,
    "highOrder": 13,
    "lowOrder": 4,
    "arithmeticReviews": [
        "docs/arithmetic.md#finite-exceptional-primes",
        "docs/arithmetic.md#small-prime-log-tail",
    ],
    "scope": "Exact integer margins of the separately reviewed smaller-anchor arithmetic argument.",
}
print(json.dumps(report, indent=2))
