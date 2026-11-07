"""Independent exact ordinary-coefficient lift, compiler and complete SOS audit."""

from pathlib import Path
from fractions import Fraction as Q
from math import gcd
import json, sys

R = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R / "tools"))
from sparse import read, digest, poly, rows, subst, add, mul

P = R / "construction/326"
B = R / "results/318/compiled-ir.json"
old = read(B)
lift = read(P / "lifted-ir.json")
cs = {c["name"]: c["id"] for c in lift["coordinates"]}
S = cs["constant.power16"]
N = cs["anchor.parityNorm.coordinate"]
T = cs["constant.anchorNormProduct"]
r = rows(lift)
prior = rows(old)
assert len(lift["coordinates"]) == 326 and len(r) == 296
for k, p in prior.items():
    assert subst(r[k], {S: {((), 1): Q(1)}, T: {((N,), 1): Q(1)}}) == p
rn = {x["name"]: poly(x["terms"]) for x in lift["residuals"]}
for k in range(10, 17):
    i = cs[f"constant.power{k}"]
    expected = (
        {((i,), 0): Q(1), ((), 0): Q(-(3**1024))}
        if k == 10
        else {
            ((i,), 0): Q(1),
            ((cs[f"constant.power{k-1}"], cs[f"constant.power{k-1}"]), 0): Q(-1),
        }
    )
    assert rn[f"constant.power{k}.definition"] == expected
assert rn["constant.anchorNormProduct.definition"] == {
    ((T,), 0): Q(1),
    (tuple(sorted([S, N])), 0): Q(-1),
}
assert len(set(r) - set(prior)) == 8
assert all(z == 0 and len(m) <= 2 for p in r.values() for m, z in p)
cert = read(R / "results/326/reduction-certificate.json")
assert cert["inputSha256"] == digest(P / "lifted-ir.json")
work = r.copy()
for op in cert["operations"]:
    assert op["kind"] == "normalize"
    c = Q(op["multiplier"])
    assert c
    work[op["residual"]] = {m: c * v for m, v in work[op["residual"]].items()}
compiled = read(R / "results/326/compiled-ir.json")
assert rows(compiled) == work
sos = {}
for p in work.values():
    sos = add(sos, mul(p, p))
cm = read(R / "results/326/coordinate-map.json")
mp = {x["sourceId"]: x["compactId"] for x in cm["mapping"]}
assert sorted(mp.values()) == list(range(326)) and mp[0] == 0
expected = {(tuple(sorted(mp[i] for i in m)), z): c for (m, z), c in sos.items()}
actual = read(R / "results/326/polynomial.json")
assert poly(actual["terms"]) == expected
assert (
    len(sos) == 3157
    and max(len(m) for m, z in sos) == 4
    and all(z == 0 and c.denominator == 1 for (m, z), c in sos.items())
)
content = 0
for c in sos.values():
    content = gcd(content, abs(c.numerator))
assert content == 1
height = max(abs(c.numerator) for c in sos.values())
offset = height - 3**2048
assert height < 2**3247
report = {
    "verdict": "PASS",
    "coordinates": 326,
    "witnesses": 325,
    "quadraticResiduals": 296,
    "monomials": 3157,
    "degree": 4,
    "content": content,
    "constantChainCoordinates": 7,
    "sharedProductCoordinates": 1,
    "allSourceResidualsReconstructed": len(prior),
    "allLiftDefinitionsChecked": 8,
    "uniqueExtension": "The seed, each successive square and the product have unique rational values. The terminal value is 3^(2^16).",
    "compilerNonzeroScalings": len(cert["operations"]),
    "maximumCoefficient": f"3^2048 + {offset}",
    "coefficientBitLength": height.bit_length(),
    "maximumCoefficientDecimalDigits": len(str(height)),
    "heightBound": "< 2^3247",
    "polynomialSHA256": digest(R / "results/326/polynomial.json"),
    "sourceSHA256": digest(B),
    "liftedSHA256": digest(P / "lifted-ir.json"),
    "inputUnchanged": True,
    "symbolicCoefficientPowers": 0,
}
print(json.dumps(report, indent=2))
