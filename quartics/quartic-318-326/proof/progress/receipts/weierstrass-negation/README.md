# Actual global Weierstrass Scheme involution

Three modules construct and identify the actual global negation automorphism of the genuine two-chart glued curve.

`ChartNegation318` constructs the actual quotient-algebra maps (x,y)↦(x,−y) on the finite chart and (x,z)↦(−x,−z) on the infinity chart. It proves their squares are the identity. The localized overlap map is constructed by the localization universal property; its inverse coordinate also changes sign. Exact compatibility with the genuine chart-transition maps is proved.

`GluedNegation318` uses the actual Scheme pushout universal property to descend those two maps. It proves the resulting global morphism squares to the identity, gives a genuine Scheme automorphism, preserves the original base structure morphism and fixes the actual infinity section. These are identities of Scheme morphisms, not just pointwise equalities. The literal OpenJ specialization is included. The construction works in every characteristic over every commutative base ring.

`NegationPoints318` proves the exact finite-chart evaluation formula and identifies the resulting operation with Mathlib's genuine point negation on every field specialization of the literal source model. Actual nonsingularity is inherited from the prior field-point bridge, not supplied separately.

Strict replay and full recursive audit: 46 declarations across three modules, 26 public theorems, standard axioms only. Replay: `bash run.sh`.

Remaining boundary: this global involution does not itself construct a full relative group law. Tangent/infinity addition, compatibility across all group-law charts, relative torsion schemes and the specified modular-family identification remain separate. Projective/proper identification is handled in a distinct packet.
