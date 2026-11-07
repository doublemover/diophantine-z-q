"""Replace the fixed anchor by a unique short squaring chain and one product."""

from pathlib import Path
from fractions import Fraction as Q
from copy import deepcopy
import sys, json

R = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R / "tools"))
from sparse import read, digest, poly, subst, rows

P = Path(__file__).parent
src = R / "results/318/compiled-ir.json"
old = read(src)
new = deepcopy(old)
assert old["fixedParameter"]["value"] == "3^(2^16)"
N = next(
    c["id"] for c in old["coordinates"] if c["name"] == "anchor.parityNorm.coordinate"
)
nextid = max(c["id"] for c in old["coordinates"]) + 1
chain = {k: nextid + k - 10 for k in range(10, 17)}
S = chain[16]
product = nextid + 7
for k, i in chain.items():
    new["coordinates"].append(
        {
            "id": i,
            "name": f"constant.power{k}",
            "kind": "auxiliary",
            "protected": True,
            "block": "constant_lift",
        }
    )
new["coordinates"].append(
    {
        "id": product,
        "name": "constant.anchorNormProduct",
        "kind": "auxiliary",
        "protected": True,
        "block": "constant_lift",
    }
)


def encode(p):
    return [
        {"monomial": list(m), "sPower": z, "coefficient": str(c)}
        for (m, z), c in sorted(p.items())
        if c
    ]


for row in new["residuals"]:
    out = {}
    for (m, z), c in poly(row["terms"]).items():
        mm = list(m)
        while z and N in mm:
            mm.remove(N)
            mm.append(product)
            z -= 1
        mm += [S] * z
        key = (tuple(sorted(mm)), 0)
        out[key] = out.get(key, Q(0)) + c
    assert all(len(m) <= 2 for m, z in out)
    row["terms"] = encode(out)
rid = max(r["id"] for r in old["residuals"]) + 1
for k, i in chain.items():
    p = (
        {((i,), 0): Q(1), ((), 0): Q(-(3**1024))}
        if k == 10
        else {((i,), 0): Q(1), ((chain[k - 1], chain[k - 1]), 0): Q(-1)}
    )
    new["residuals"].append(
        {
            "id": rid,
            "name": f"constant.power{k}.definition",
            "kind": "structural",
            "block": "constant_lift",
            "terms": encode(p),
        }
    )
    rid += 1
new["residuals"].append(
    {
        "id": rid,
        "name": "constant.anchorNormProduct.definition",
        "kind": "structural",
        "block": "constant_lift",
        "terms": encode({((product,), 0): Q(1), (tuple(sorted([S, N])), 0): Q(-1)}),
    }
)
new.pop("sourceGates", None)
new["gates"] = []
new["values"] = {}
new["fixedParameter"] = {
    "name": "S",
    "value": "3^(2^16)",
    "coordinate": True,
    "coordinateId": S,
    "description": "Uniquely forced by the appended rational squaring chain; no symbolic coefficients remain.",
}
new["variant"] = {
    "name": "decimal_326",
    "predecessor": str(src),
    "predecessorSHA256": digest(src),
    "method": "Unique squaring chain from 3^1024 to 3^(2^16), plus one shared anchor product",
    "status": "pending_independent_replay",
}
new["counts"] = {
    "coordinates": len(new["coordinates"]),
    "residuals": len(new["residuals"]),
    "gates": 0,
}
(P / "lifted-ir.json").write_text(json.dumps(new, indent=2) + "\n")
(P / "lift-certificate.json").write_text(
    json.dumps(
        {
            "source": str(src),
            "sourceSHA256": digest(src),
            "targetSHA256": digest(P / "lifted-ir.json"),
            "chain": chain,
            "productCoordinate": product,
            "normCoordinate": N,
            "constantSeed": "3^1024",
            "fixedTarget": "3^(2^16)",
            "newCoordinates": 8,
            "allResidualsQuadratic": True,
        },
        indent=2,
    )
    + "\n"
)
print(new["counts"])
