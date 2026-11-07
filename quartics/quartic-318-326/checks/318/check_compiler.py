"""Independent constant-pivot compiler-certificate replay.
Uses exact sparse-polynomial arithmetic.
"""

from pathlib import Path
from fractions import Fraction as Q
import json
import sys

sys.path.insert(0, str((Path(__file__).resolve().parents[2] / "tools")))
from sparse import read, digest, poly, rows, subst, add

D = Path(__file__).resolve().parents[2] / "construction/318"
raw = read(D / "raw-ir.json")
translated = read(D / "raw-translated-ir.json")
r = rows(raw)
t = rows(translated)
anchor = raw["anchor"]["rowId"]
u, v, w = raw["anchor"]["privateCoordinateIds"]
images = {
    u: {((), 1): Q(1), ((u,), 0): Q(1, 4), ((v,), 0): Q(-3, 4), ((w,), 0): Q(3, 4)},
    v: {((), 1): Q(1, 2), ((v,), 0): Q(1, 4)},
    w: {((), 1): Q(3, 2), ((w,), 0): Q(1, 4)},
}
expected = {k: 16 * c for k, c in subst(r[anchor], images).items()}
assert t[anchor] == expected
assert all(r[i] == t[i] for i in r if i != anchor)
assert raw["counts"] == translated["counts"]
cert = read(D / "compiled/reduction-certificate.json")
assert cert["inputSha256"] == digest(D / "raw-translated-ir.json")
work = dict(t)
coordinates = {c["id"] for c in translated["coordinates"]}
elim = []
normalized = 0
for op in cert["operations"]:
    if op["kind"] == "normalize":
        k = op["residual"]
        c = Q(op["multiplier"])
        assert c
        work[k] = {m: a * c for m, a in work[k].items()}
        normalized += 1
    elif op["kind"] == "eliminate":
        k = op["pivot"]
        v = op["coordinate"]
        p = work[k]
        a = p[((v,), 0)]
        assert a == Q(op["coefficient"]) and a
        assert all(v not in m or (m == (v,) and s == 0) for m, s in p)
        replacement = {m: -c / a for m, c in p.items() if m != ((v,), 0)}
        assert replacement == poly(op["replacement"])
        affected = sorted(
            i for i, p in work.items() if i != k and any(v in m for m, s in p)
        )
        assert affected == sorted(op["affected"])
        assert subst(work[k], {v: replacement}) == {}
        del work[k]
        coordinates.remove(v)
        for i in affected:
            work[i] = subst(work[i], {v: replacement})
        assert all(len(m) <= 2 for i in affected for m, s in work[i])
        elim.append(v)
    else:
        raise AssertionError(op["kind"])
final = read(D / "compiled/compiled-ir.json")
assert rows(final) == work
assert {c["id"] for c in final["coordinates"]} == coordinates
report = {
    "verdict": "PASS",
    "method": "Independent exact polynomial replay of every certificate operation, deriving replacements from pivots rather than trusting them.",
    "sourceSha256": digest(D / "raw-translated-ir.json"),
    "targetSha256": digest(D / "compiled/compiled-ir.json"),
    "anchorTranslationIdentity": "new row = 16 * old row after invertible rational substitution; determinant 1/64",
    "eliminations": len(elim),
    "nonzeroRowScalings": normalized,
    "finalCoordinates": len(coordinates),
    "finalResiduals": len(work),
    "maxResidualDegree": max(len(m) for p in work.values() for m, s in p),
    "inputUnchanged": 0 in coordinates and 0 not in elim,
    "scope": "Exact projection equivalence of the named raw translated system and its compiled output.",
}
print(json.dumps(report, indent=2))
