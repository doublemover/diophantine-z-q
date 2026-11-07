"""Expand and check every coefficient of the 318-variable polynomial."""

from pathlib import Path
from collections import defaultdict
from fractions import Fraction as Q
from math import gcd
import json
import sys

sys.path.insert(0, str((Path(__file__).resolve().parents[2] / "tools")))
from sparse import read, digest, poly, rows, add, mul

D = Path(__file__).resolve().parents[2] / "construction/318"
C = Path(__file__).resolve().parents[2] / "results/318"
s = read(C / "compiled-ir.json")
out = read(C / "polynomial.json")
cm = read(C / "coordinate-map.json")
assert s["fixedParameter"]["value"] == "3^(2^16)"
assert out["fixedParameter"] == "S = 3^(2^16)"
rs = rows(s)
assert len(s["coordinates"]) == 318 and len(rs) == 288
assert all(len(m) <= 2 for p in rs.values() for m, z in p)
sos = {}
for p in rs.values():
    sos = add(sos, mul(p, p))
ids = {c["id"] for c in s["coordinates"]}
used = {i for m, z in sos for i in m}
assert ids == used and not cm["omittedFreeCoordinates"]
mp = {m["sourceId"]: m["compactId"] for m in cm["mapping"]}
assert set(mp) == ids and sorted(mp.values()) == list(range(318)) and mp[0] == 0
compacted = {(tuple(sorted(mp[i] for i in m)), z): c for (m, z), c in sos.items()}
assert poly(out["terms"]) == compacted
assert all(c.denominator == 1 for c in sos.values())
by = defaultdict(dict)
for (m, z), c in sos.items():
    by[m][z] = c
assert len(by) == 3134 and max(len(m) for m in by) == 4
content = 0
for p in by.values():
    if set(p) == {0}:
        content = gcd(content, abs(p[0].numerator))
assert content == 1
B = Q(2**4096)


def clean(p):
    return {k: v for k, v in p.items() if v}


def pos(p):
    p = clean(p)
    if not p:
        return False
    k = max(p)
    return p[k] > sum(abs(v) / B ** (k - j) for j, v in p.items() if j < k)


absolute = {}
for m, p in by.items():
    sign = 1 if p[max(p)] > 0 else -1
    absolute[m] = {k: sign * v for k, v in p.items()}
    assert pos(absolute[m])
kmax = max(z for m, z in sos)
best = max(
    absolute.values(), key=lambda p: tuple(p.get(k, Q(0)) for k in range(kmax, -1, -1))
)
for p in absolute.values():
    diff = clean({k: best.get(k, Q(0)) - p.get(k, Q(0)) for k in set(best) | set(p)})
    assert not diff or pos(diff)
report = {
    "verdict": "PASS",
    "method": "Independent sparse-polynomial expansion of every residual square and comparison of every specialized coefficient polynomial.",
    "rawTranslatedSha256": digest(D / "sheared-ir.json"),
    "compiledIrSha256": digest(C / "compiled-ir.json"),
    "polynomialSha256": digest(C / "polynomial.json"),
    "coordinates": len(ids),
    "witnesses": len(ids) - 1,
    "quadraticResiduals": len(rs),
    "monomials": len(by),
    "parameterCoefficientTerms": len(sos),
    "degree": 4,
    "primitiveIntegerContent": 1,
    "inputUnchanged": True,
    "maxSPower": kmax,
    "fixedParameter": "S=3^(2^16), not a coordinate",
    "exactCoefficientHeightPolynomial": {
        str(k): str(v) for k, v in sorted(best.items(), reverse=True)
    },
    "coefficientComparisonThreshold": "S>=2^4096, satisfied by the fixed S",
    "scope": "Exact quartic artifact and coefficient statistics. Arithmetic source transformations are separately audited and retain upstream assumptions.",
}
print(json.dumps(report, indent=2))
