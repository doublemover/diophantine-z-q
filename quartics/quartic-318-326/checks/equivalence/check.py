from pathlib import Path
from fractions import Fraction as Q
import json, hashlib, sys, re

R = Path(__file__).resolve().parents[2]
B = R / "construction/318"
C = R / "construction/326"
OUT = Path(__file__).parent
if len(sys.argv) > 1:
    B = Path(sys.argv[1])
    C = Path(sys.argv[2])
    OUT = Path(sys.argv[3])
    OUT.mkdir(parents=True, exist_ok=True)


def read(p):
    return json.loads(p.read_text())


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def poly(ts):
    return {(int(t["sPower"]), tuple(t["monomial"])): Q(t["coefficient"]) for t in ts}


def add(p, q):
    r = p.copy()
    for k, v in q.items():
        r[k] = r.get(k, Q(0)) + v
        if not r[k]:
            del r[k]
    return r


def mul(p, q):
    r = {}
    for (s, m), v in p.items():
        for (t, n), w in q.items():
            r = add(r, {(s + t, tuple(sorted(m + n))): v * w})
    return r


def subst(p, mp):
    r = {}
    for (s, m), v in p.items():
        z = {(s, ()): v}
        for i in m:
            z = mul(z, mp.get(i, {(0, (i,)): Q(1)}))
        r = add(r, z)
    return r


def rows(j):
    return {r["id"]: poly(r["terms"]) for r in j["residuals"]}


def replay(src, dest, cert):
    work = rows(src)
    for op in cert["operations"]:
        assert op["kind"] == "normalize", op["kind"]
        c = Q(op["multiplier"])
        assert c
        work[op["residual"]] = {k: c * v for k, v in work[op["residual"]].items()}
    assert work == rows(dest)
    return len(work)


b = read(B / "raw-translated-ir.json")
assert b["fixedParameter"]["value"] == "3^(2^16)"
fixed = b["fixedParameter"]["value"]
power = int(re.fullmatch(r"3\^\(2\^(\d+)\)", fixed).group(1))
bc = read(B / "compiled/compiled-ir.json")
sh = read(B / "sheared-ir.json")
cert = read(B / "shear-certificate.json")
u = cert["coordinate"]
n = cert["normCoordinate"]
fwd = {u: {(0, (u,)): Q(1), (1, (n,)): Q(-1)}, n: {(0, (n,)): Q(1, 4096)}}
inv = {u: {(0, (u,)): Q(1), (1, (n,)): Q(4096)}, n: {(0, (n,)): Q(4096)}}
for rid, p in rows(bc).items():
    q = subst(p, fwd)
    assert q == rows(sh)[rid]
    assert subst(q, inv) == p
    assert max(map(lambda x: len(x[1]), q), default=0) <= 2
shc = read(R / "results/318/compiled-ir.json")
replay(sh, shc, read(R / "results/318/reduction-certificate.json"))
lift = read(C / "lifted-ir.json")
lc = read(C / "lift-certificate.json")
chain = {int(k): v for k, v in lc["chain"].items()}
ss = chain[power]
t = lc["productCoordinate"]
assert n == lc["normCoordinate"]
for rid, p in rows(shc).items():
    assert subst(rows(lift)[rid], {ss: {(1, ()): Q(1)}, t: {(1, (n,)): Q(1)}}) == p
names = {x["name"]: poly(x["terms"]) for x in lift["residuals"]}
for k, i in chain.items():
    expected = (
        {(0, (i,)): Q(1), (0, ()): Q(-(3**1024))}
        if k == 10
        else {(0, (i,)): Q(1), (0, (chain[k - 1], chain[k - 1])): Q(-1)}
    )
    assert names[f"constant.power{k}.definition"] == expected
assert names["constant.anchorNormProduct.definition"] == {
    (0, (t,)): Q(1),
    (0, tuple(sorted((ss, n)))): Q(-1),
}
assert len(lift["coordinates"]) - len(shc["coordinates"]) == len(chain) + 1
assert all(s == 0 and len(m) <= 2 for p in rows(lift).values() for s, m in p)
final = read(R / "results/326/compiled-ir.json")
replay(lift, final, read(R / "results/326/reduction-certificate.json"))
report = {
    "status": "PASS",
    "finalArithmeticRows": len(b["residuals"]),
    "invertibleShearRows": len(sh["residuals"]),
    "uniqueConstantChainCoordinates": len(chain),
    "uniqueSharedProductCoordinates": 1,
    "liftedQuadraticRows": len(lift["residuals"]),
    "sourceCount": 318,
    "liftedCount": len(lift["coordinates"]),
    "inputUnchanged": 0 not in fwd and 0 not in chain.values(),
    "fixedConstant": fixed,
    "decimalPolynomialSHA256": digest(R / "results/326/polynomial.json"),
    "scope": "Independent Fraction substitution, inverse identities, unique lift definitions and compiler row normalization. Full SOS checked separately.",
}
sos = {}
for p in rows(final).values():
    sos = add(sos, mul(p, p))
cm = read(R / "results/326/coordinate-map.json")
mp = {v["sourceId"]: v["compactId"] for v in cm["mapping"]}
assert sorted(mp.values()) == list(range(len(lift["coordinates"]))) and mp[0] == 0
expected = {(sp, tuple(sorted(mp[i] for i in m))): v for (sp, m), v in sos.items()}
actual = poly(read(R / "results/326/polynomial.json")["terms"])
assert actual == expected
assert all(sp == 0 and v.denominator == 1 for (sp, m), v in expected.items())
height = max(abs(v.numerator) for v in expected.values())
assert height == 3**2048 + 3813373282171 and height < 2**3247
report.update(
    {
        "fullOrdinarySosReplay": "PASS",
        "monomials": len(expected),
        "degree": max(len(m) for sp, m in expected),
        "maximumCoefficient": "3^2048 + 3813373282171",
        "coefficientBitLength": height.bit_length(),
        "heightBound": "<2^3247",
    }
)
# Verify the human-readable complete decimal table independently of its writer.
textfile = R / "results/326/coefficients.txt"
textterms = {}
for line in textfile.read_text().splitlines()[4:]:
    if not line.strip():
        continue
    coefficient, monomial = line.split(" | ")
    v = Q(int(coefficient))
    mm = []
    if monomial != "1":
        for factor in monomial.split(" * "):
            hit = re.fullmatch(r"x(\d+)(?:\^(\d+))?", factor)
            assert hit, factor
            mm.extend([int(hit.group(1))] * int(hit.group(2) or 1))
    key = (0, tuple(sorted(mm)))
    assert key not in textterms
    textterms[key] = v
assert textterms == actual
report.update(
    {
        "completeDecimalTextReplay": "PASS",
        "decimalTextSHA256": digest(textfile),
        "decimalTextTerms": len(textterms),
    }
)
print(json.dumps(report, indent=2))
