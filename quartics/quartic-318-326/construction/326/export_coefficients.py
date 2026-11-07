from pathlib import Path
import json

result = Path(__file__).resolve().parents[2] / "results/326"
polynomial = json.loads((result / "polynomial.json").read_text())
lines = [
    "# Quartic in 326 rational variables",
    "Variables x0 through x325; x0 is the input.",
    "Each line is: integer coefficient | monomial.",
    "",
]
for term in sorted(polynomial["terms"], key=lambda term: term["monomial"]):
    monomial = term["monomial"]
    factors = [
        f"x{i}" + (f"^{monomial.count(i)}" if monomial.count(i) > 1 else "")
        for i in sorted(set(monomial))
    ]
    lines.append(
        term["coefficient"].removesuffix("/1") + " | " + (" * ".join(factors) or "1")
    )
(result / "coefficients.txt").write_text("\n".join(lines) + "\n")
