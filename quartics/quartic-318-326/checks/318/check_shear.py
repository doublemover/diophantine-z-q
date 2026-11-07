from pathlib import Path
from fractions import Fraction as Q
import sys, json

R = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R / "tools"))
from sparse import read, digest, poly, rows, subst

P = R / "construction/318"
original = read(
    (Path(__file__).resolve().parents[2] / "construction/318/compiled/compiled-ir.json")
)
target = read(P / "sheared-ir.json")
u = 308
n = 145
forward = {u: {((u,), 0): Q(1), ((n,), 1): Q(-1)}, n: {((n,), 0): Q(1, 4096)}}
inverse = {u: {((u,), 0): Q(1), ((n,), 1): Q(4096)}, n: {((n,), 0): Q(4096)}}
assert (
    original["coordinates"][0]["name"] == "input"
    and target["coordinates"][0]["name"] == "input"
)
o = rows(original)
t = rows(target)
assert set(o) == set(t)
for k, p in o.items():
    assert subst(p, forward) == t[k]
    assert subst(t[k], inverse) == p
    assert all(len(m) <= 2 for m, s in t[k])
assert set(c["id"] for c in original["coordinates"]) == set(
    c["id"] for c in target["coordinates"]
)
cert = read(R / "results/318/reduction-certificate.json")
assert cert["inputSha256"] == digest(P / "sheared-ir.json")
work = t.copy()
for op in cert["operations"]:
    assert op["kind"] == "normalize"
    factor = Q(op["multiplier"])
    assert factor
    work[op["residual"]] = {k: factor * v for k, v in work[op["residual"]].items()}
assert work == rows(read(R / "results/318/compiled-ir.json"))
report = {
    "verdict": "PASS",
    "sourceSha256": digest(
        (
            Path(__file__).resolve().parents[2]
            / "construction/318/compiled/compiled-ir.json"
        )
    ),
    "shearedSha256": digest(P / "sheared-ir.json"),
    "compiledSha256": digest(R / "results/318/compiled-ir.json"),
    "coordinates": len(target["coordinates"]),
    "checkedRows": len(o),
    "inverseIdentities": True,
    "inputUnchanged": True,
    "compilerNonzeroScalings": len(cert["operations"]),
    "scope": "Exact fixed-S affine bijection and every compiler operation.",
}
print(json.dumps(report, indent=2))
