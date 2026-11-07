# Actual homogeneous-equation Galois descent

Four public theorems, four exhaustively audited declarations, strict kernel PASS. This is a separate strengthening of the frozen projective-galois-descent packet.

`eval₂_scale` derives the actual evaluation scaling p(c*x)=c^degree*p(x) directly from homogeneous support degrees. `rational_equations_of_scaled` then uses the injective base-field map to prove that normalized rational coordinates satisfy the actual original multivariate-polynomial equations.

`equations_descend` descends a nonzero coordinate vector and an arbitrary family of homogeneous equations simultaneously. `projective_zero_descend` starts with an actual Mathlib projective point fixed by all automorphisms of a finite Galois extension, whose representative satisfies the original equations. It produces a nonzero base-field vector satisfying those equations and proves its actual projective base change equals the original point. Rationality and membership are both conclusions, not premises.

The actual canonical curve and projective embedding must still be constructed. When its defining equations are supplied, this packet removes a separate geometric-point membership assertion from the finite-Galois descent step. It does not construct a genus-zero splitting or an actual Shimura scheme.

Run bash build.sh for strict source replay and exhaustive standard-axiom audit. Only propext, Classical.choice and Quot.sound occur. Frozen predecessor files were not modified.
