# Exceptional-divisor negativity

Status: strict-kernel PASS. Six public theorems, seven recursively audited declarations, standard axioms only.

The exact matrix theorem `effective_of_matrix_nonpos` says: if a real intersection matrix M has nonnegative off-diagonal entries and −M is positive definite in Mathlib's actual quadratic-form sense, then Mz≤0 implies z≥0 coefficientwise. It does not assume a sign property for M inverse.

The proof forms the positive and negative parts z=p−n, whose supports are disjoint. Their cross-intersection is nonnegative because diagonal terms vanish and distinct-component intersections are nonnegative. The hypothesis gives n·Mn≥n·Mp≥0; actual negative definiteness makes this impossible unless n=0.

`canonical_coefficients_le` states the exact D−K coefficient conclusion. `canonical_domination_with_outside` also constructs the nonnegative contribution of effective nonexceptional components from their finite cross-intersection matrix. These cover the sign and linear-algebra step in docs/arithmetic.md, “Extending the inequality across exceptional curves.”

To apply this to arithmetic surfaces, the actual regular model, finite exceptional component set, intersection matrices, negative definiteness, distinct-component intersection positivity, and the adjunction/pullback intersection inequalities must still be supplied. This packet does not construct those geometric objects and does not prove FiveContact49Height.

Replay: `bash run.sh`; the exhaustive audit is in build.log.
