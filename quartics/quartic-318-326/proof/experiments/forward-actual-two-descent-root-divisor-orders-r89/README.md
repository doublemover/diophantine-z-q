# Algebraic norm transfer and strict coefficient descent

One native-only source is added. It proves the literal homogeneous witness-ascent identity, affine norm transfer over every field when the relevant denominator is nonzero, and strict coefficient shrink after an integer centered modular root is supplied. These are constructive algebraic and arithmetic steps used by classical ternary descent.

All1342 predecessor sources and their relative order remain byte-identical. The new source imports only native Mathlib.Tactic, so its experiment closure is one root. No full induction or unchecked experiment dependency is included.

The hypotheses t²-a=b*c, relevant nonzero denominator and centered-size inequalities remain explicit. Modular root existence and all-place inputs are not asserted by this leaf. The separate full ternary induction still requires strict testing after this checkpoint; the actual quaternary auxiliary selection and four elliptic realizations remain separate. Source review is not Lean acceptance.
