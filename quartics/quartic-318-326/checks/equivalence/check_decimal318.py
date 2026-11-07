"""Independent literal318 export audit using integer arithmetic only."""

from pathlib import Path
from fractions import Fraction
from math import gcd
import sys, json, hashlib, re

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "construction/318"
OUT = Path(__file__).parent
S = 3**65536


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def specialize(terms):
    out = {}
    for term in terms:
        value = Fraction(term["coefficient"]) * S ** term["sPower"]
        assert value.denominator == 1
        key = tuple(term["monomial"])
        out[key] = out.get(key, 0) + value.numerator
    return {key: value for key, value in out.items() if value}


compiled = read(ROOT / "results/318/compiled-ir.json")
assert compiled["fixedParameter"]["value"] == "3^(2^16)"
cm = read(ROOT / "results/318/coordinate-map.json")
mapping = {x["sourceId"]: x["compactId"] for x in cm["mapping"]}
assert mapping[0] == 0 and sorted(mapping.values()) == list(range(318))
sos = {}
for row in compiled["residuals"]:
    p = specialize(row["terms"])
    for a, u in p.items():
        for b, v in p.items():
            key = tuple(sorted(mapping[i] for i in a + b))
            sos[key] = sos.get(key, 0) + u * v
sos = {key: value for key, value in sos.items() if value}
source = read(ROOT / "results/318/polynomial.json")
assert specialize(source["terms"]) == sos
literal = read(ROOT / "results/318/coefficients.json")
assert literal["sourcePolynomialSHA256"] == digest(ROOT / "results/318/polynomial.json")
actual = {tuple(t["monomial"]): int(t["coefficient"]) for t in literal["terms"]}
assert len(actual) == len(literal["terms"]) and actual == sos
textterms = {}
for line in (ROOT / "results/318/coefficients.txt").read_text().splitlines()[4:]:
    if not line.strip():
        continue
    coefficient, monomial = line.split(" | ")
    m = []
    if monomial != "1":
        for factor in monomial.split(" * "):
            match = re.fullmatch(r"x(\d+)(?:\^(\d+))?", factor)
            assert match
            m.extend([int(match.group(1))] * int(match.group(2) or 1))
    key = tuple(sorted(m))
    assert key not in textterms
    textterms[key] = int(coefficient)
assert textterms == sos
content = 0
for coefficient in sos.values():
    content = gcd(content, abs(coefficient))
height = max(map(abs, sos.values()))
assert height == 64 * S * S and content == 1
assert len(sos) == 3134 and max(map(len, sos)) == 4
report = {
    "status": "PASS",
    "coordinates": 318,
    "witnesses": 317,
    "quadraticRowsResquared": len(compiled["residuals"]),
    "degree": 4,
    "monomials": len(sos),
    "primitiveContent": content,
    "fixedConstant": "3^(2^16)",
    "largestCoefficient": "64 * 3^(2^17)",
    "largestCoefficientDecimalDigits": len(str(height)),
    "literalJsonSHA256": digest(ROOT / "results/318/coefficients.json"),
    "literalTextSHA256": digest(ROOT / "results/318/coefficients.txt"),
    "scope": "Independent integer specialization, resquaring of every compiled row, and parsing of both complete decimal exports.",
}
print(json.dumps(report, indent=2))
