# Actual modular transport of the Weierstrass torus and torsion labels

For every actual g in SL₂(Z), tau in the upper half-plane and complex argument z, this packet binds the actual normalized-model coordinate transport to the actual lattice parametrization at z/(c tau+d).

1. The explicit integer period-coordinate formulas prove a genuine bijection between the two actual lattices. No lattice-scaling premise is supplied.
2. Reindexing the actual Mathlib Weierstrass series proves the exact square and cube scaling of ℘ and ℘′, including their conventions at lattice points.
3. The existing model point transport therefore equals the genuine point map after division by c tau+d, including infinity. Its addition law follows from the already checked genuine Weierstrass addition theorem. The literal map between period quotients is shown to be an additive equivalence, and the point diagram commutes.
4. For every positive N, the actual N-torsion labels transform by the inverse-transpose matrix [[d,-c],[-b,a]], in column coordinates relative to (tau,1). This is an additive equivalence of residue-label groups. Exact order and primitivity are preserved.

The inverse-transpose convention is derived from the actual period identities, rather than inferred from a generic matrix-action convention.

## Boundary

This closes the concrete complex-point, group, lattice and torsion-coordinate compatibility. It does not construct the relative modular scheme/family, its finite étale torsion cover, a Weil pairing, a global manifold registration, or an arithmetic model.

## Replay

Run `bash run.sh`. The four source modules and exhaustive recursive axiom audit are rebuilt with `debug.skipKernelTC=false`. Only propext, Classical.choice and Quot.sound are allowed.
