# Actual projective Galois descent for the five inertia labels

Strict kernel replay passes all 12 declarations in one module, including six public theorems. Only propext, Classical.choice and Quot.sound occur.

The packet uses Mathlib's actual Projectivization, its actual semilinear maps, and the actual finite-Galois fixed-field theorem. Given an actual projective point fixed by every F-automorphism of a finite Galois extension E/F, it derives a nonzero coordinate vector over F whose actual projective base change equals that point. No rationality or rational-coordinate-ratio premise is supplied.

The proof chooses a nonzero coordinate x_j. Projective invariance gives sigma(x)=c_sigma*x with a unit c_sigma, so all x_i/x_j are fixed. The Galois fixed-field theorem places every ratio in F. The resulting vector is nonzero because its j-coordinate is one. The exact projective equality then follows from the actual quotient relation.

`five_labelled_points_descend` composes this descent with the proved injectivity of the five literal inertia labels 30,42,70,105,210. An actual permutation of the five points preserving those labels is the identity. Actual Galois-equivariant projective coordinates therefore descend point by point.

## Exact application boundary

The actual curve over F, an embedding into projective space, the five ramification orbits, and the compatibility of Galois action with the Q-defined Atkin-Lehner labels still have to be supplied by the canonical-model construction. The theorem does not construct that curve, assert that a genus-zero curve is already split, or assume a P1 coordinate. The ambient projective dimension is arbitrary. Descent of the embedded point is therefore available before selecting a rational coordinate on the genus-zero quotient.

`bash build.sh` replays the source with debug.skipKernelTC=false and exhaustively audits the module's declarations. It uses the shared Mathlib cache and frozen InertiaLabels318 dependency. It is not a fresh replay of every imported Mathlib declaration.
