"""Materialize every integer coefficient of the accepted 318-variable quartic."""

from pathlib import Path
from fractions import Fraction
from collections import defaultdict
from math import gcd
import hashlib, json, sys

sys.set_int_max_str_digits(0)
P = Path(__file__).parent
source = P.parents[1] / "results/318/polynomial.json"
j = json.loads(source.read_text())
S = 3 ** (2**16)
coefficients = defaultdict(int)
for t in j["terms"]:
    c = Fraction(t["coefficient"]) * S ** t["sPower"]
    assert c.denominator == 1
    coefficients[tuple(t["monomial"])] += c.numerator
coefficients = {m: c for m, c in coefficients.items() if c}
content = gcd(*coefficients.values())
out = P.parents[1] / "results/318"
out.mkdir(exist_ok=True)
data = {
    "schema": "quartic-decimal-integer-table-v1",
    "variables": 318,
    "inputVariable": 0,
    "degree": 4,
    "monomials": len(coefficients),
    "primitiveContent": content,
    "sourcePolynomialSHA256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "terms": [
        {"monomial": list(m), "coefficient": str(c)}
        for m, c in sorted(coefficients.items())
    ],
}
jsonpath = out / "coefficients.json"
jsonpath.write_text(json.dumps(data, indent=2) + "\n")
lines = [
    "# Quartic in 318 rational variables",
    "Variables x0 through x317; x0 is the input.",
    "Each line is: integer coefficient | monomial.",
    "",
]
for m, c in sorted(coefficients.items()):
    factors = [
        f"x{i}" + (f"^{m.count(i)}" if m.count(i) > 1 else "") for i in sorted(set(m))
    ]
    lines.append(str(c) + " | " + (" * ".join(factors) or "1"))
txtpath = out / "coefficients.txt"
txtpath.write_text("\n".join(lines) + "\n")
