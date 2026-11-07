# Actual glued Weierstrass relative dimension one

Two strict-kernel-checked modules prove that the actual two-chart scheme pushout is smooth of relative dimension one.

`InfinityRelativeDimension318` constructs both one-equation/two-variable Jacobian presentations of the actual Y=1 quotient ring. It proves the exact identity

2 = (2 - (2 A x + 3 B z) z) F_z - (2 A x + 3 B z) x F_x.

Thus the two minors span the unit ideal whenever 2 is a unit, without a discriminant hypothesis for this chart. The genuine local standard-smooth presentations have dimension 1.

`GluedRelativeDimension318` uses the actual pushout open cover and the finite-chart dimension theorem to prove relative dimension one for the whole glued family, assuming 2 and the discriminant are units. Its literal OpenJModel specialization is unconditional.

The accepted scope is the actual Scheme structure morphism, not merely pointwise equations. Projective/proper identification, a relative group law, torsion schemes and arithmetic modular-family interpretation remain separate.

Replay: `bash run.sh`. Full recursive axiom audit: 14 declarations across two modules; only propext, Classical.choice and Quot.sound.
