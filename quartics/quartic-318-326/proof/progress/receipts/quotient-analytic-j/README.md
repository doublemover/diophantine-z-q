# Actual holomorphic j-map on the fine-level quotient

Fresh strict-kernel replay and recursive audit pass all 14 declarations in two modules. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

`QuotientJ318.jMap N` is the actual modular j-function descended to the genuine Gamma1(N) orbit quotient of the upper half-plane. Its invariance is derived from the actual E4 and discriminant transformation laws. `j_holomorphic` derives complex analyticity from the genuine modular forms and the nonvanishing modular discriminant.

For N >= 5, `HolomorphicQuotientJ318.jMap_holomorphic` proves the descended function holomorphic for the already constructed complex analytic quotient atlas. The proof uses actual inverse sheets and their proved holomorphy. `jMap_localInverse` and `local_qj` give exact local formulas, including the genuine qj numerator G.

At every lift, `jMap_curve_j` identifies the value with the actual algebraic j-invariant of `ModularWeierstrass318.curve`. `curveAt` selects an actual elliptic Weierstrass model at each quotient point; `curveAt_j` proves that its j is the canonical quotient value, and `lift_model_invariant` proves independence from the selected lift at the invariant level. This does not assert that the chosen coefficient function is a global holomorphic family.

Remaining scope: no analytification comparison with the specified finite-etale algebraic source, no compactification/cusp extension, no properness/finiteness/surjectivity of this analytic map, and no arithmetic/PEL source identification is claimed. The analytic quotient and actual model invariant are genuine source-binding data, not replacements for those remaining comparisons.

Replay: `bash build-all.sh` in the existing pinned Lean 4.35 / Mathlib environment. Frozen upstream dependency hashes are recorded in receipt.json.
