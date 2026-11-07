# Independent unramified different review

Copied strict replay passed all25 declarations of UnramifiedDifferent318 with standard axiom roots only. There are three public theorems and a constructor; most additional declarations are data projections. Exact frozen source identity was verified. The imported local data/different theory was reused from checked caches.

The first theorem applies Mathlib's actual unramified-at-closed-point/different criterion. In the local DVR target, a proper different ideal lies in the maximal ideal, equivalently is divisible by it. Actual unramifiedness forbids that divisibility, forcing the different ideal to be the unit ideal. The generator of that ideal is consequently a unit, so its normalized DVR valuation and the defined different exponent are zero. No zero coefficient or zero exponent is supplied to these theorems.

The Data record requires the actual finite integral local extension, actual IsUnramifiedAt certificate and identification of the canonical coefficient with the actual different exponent. Its canonical_zero theorem derives the missing zero coefficient and the constructor feeds the frozen unramified CoefficientData branch. The nonnegative pullback coefficient remains a separate model fact. The fraction-field algebra/separability instances match the actual LocalExtension structures and were kernel checked.

Result: accepted. This closes the zero-different arithmetic antecedent for unramified components, not the geometric proof that a particular model map is unramified or the construction of its canonical divisor. No stronger global realization claim is made.
