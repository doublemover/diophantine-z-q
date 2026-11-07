from pathlib import Path
from fractions import Fraction as F
import sys, json, copy

R = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(R / "tools"))
from sparse import read, digest, poly, subst, rows

src = R / "construction/318/compiled/compiled-ir.json"
b = read(src)
out = Path(__file__).parent
ns = {c["name"]: c["id"] for c in b["coordinates"]}
u = ns["scalar.normUR"]
n = (
    ns["heightRootProduct.norm.quadratic"]
    if "heightRootProduct.norm.quadratic" in ns
    else ns["heightRootProduct.norm"]
)
# Physical NUR is exactly coordinate u; semantic n is coordinate n.
assert poly(b["values"]["scalar.normUR"]["terms"]) == {((u,), 0): F(1)}
assert poly(b["values"]["heightRootProduct.norm"]["terms"]) == {((n,), 0): F(1)}
fwd = {u: {((u,), 0): F(1), ((n,), 1): F(-1)}, n: {((n,), 0): F(1, 4096)}}
inv = {u: {((u,), 0): F(1), ((n,), 1): F(4096)}, n: {((n,), 0): F(4096)}}


def terms(p):
    return [
        {"monomial": list(m), "sPower": z, "coefficient": str(c)}
        for (m, z), c in sorted(p.items())
    ]


c = copy.deepcopy(b)
for row in c["residuals"]:
    p = poly(row["terms"])
    q = subst(p, fwd)
    assert subst(q, inv) == p
    assert all(len(m) <= 2 for m, z in q)
    row["terms"] = terms(q)
for name, v in c.get("values", {}).items():
    v["terms"] = terms(subst(poly(v["terms"]), fwd))
for coordinate in c["coordinates"]:
    if coordinate["id"] == u:
        coordinate["name"] = "anchor.physicalA.coordinate"
    if coordinate["id"] == n:
        coordinate["name"] = "anchor.parityNorm.coordinate"
# Source gate records would be stale after a coordinate shear; equations/certificate are authoritative.
c.pop("sourceGates", None)
c["gates"] = []
c["variant"] = {
    "name": "exact_fixed_parameter_anchor_value_shear",
    "status": "finite_artifact_audit_pending",
    "sourceSha256": digest(src),
    "scope": "Invertible affine coordinate shear over Q[S]; no arithmetic source relaxation.",
}
assert 0 not in fwd
(out / "sheared-ir.json").write_text(json.dumps(c, indent=2) + "\n")
certificate = {
    "source": str(src),
    "sourceSha256": digest(src),
    "targetSha256": digest(out / "sheared-ir.json"),
    "coordinate": u,
    "normCoordinate": n,
    "forward": "old Norm(uR) = new physicalA - S*new parityNorm; old Norm(product h) = new parityNorm/4096",
    "inverse": "new physicalA = old Norm(uR) + 4096*S*Norm(product h); new parityNorm = 4096*Norm(product h)",
    "fixedS": "3^(2^16)",
    "coordinates": len(c["coordinates"]),
    "rows": len(c["residuals"]),
    "everyRowInverseIdentity": True,
    "inputUnchanged": True,
    "quadratic": True,
    "ordinaryDecimalLiftWarning": "If S is promoted to a coordinate, bilinear consumers may become cubic; this certificate only concerns the fixed integer S.",
}
(out / "shear-certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")
print(json.dumps(certificate, indent=2))
