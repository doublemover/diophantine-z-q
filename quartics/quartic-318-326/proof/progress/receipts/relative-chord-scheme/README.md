# Actual relative ordinary-chord addition

Three modules construct the ordinary-chord addition morphism on the genuine affine self-fiber-product, rather than infer a scheme map from a field-valued group identity.

`RelativeChordAlgebra318` uses the exact coordinate quotient F=R[x,y]/(y²−x³−Ax−B), its actual tensor algebra F⊗[R]F and localization at x₂−x₁. The two points satisfy the equation by their actual quotient maps. The gap is a unit by localization. The usual slope and output coordinates are defined with this actual inverse. A universal polynomial identity, valid over every commutative ring, proves the output equation. This yields a genuine R-algebra map F→ChordRing with exact output coordinates. No field/domain/2-unit/discriminant assumption is used for this construction.

`RelativeChordScheme318` identifies Spec(ChordRing) as an actual open subscheme of the genuine affine self-fiber-product via Mathlib's tensor/pullback isomorphism. It constructs the actual addition Scheme morphism, proves it is over the original base and proves both actual input projection identities. Evaluation is composition with the coordinate algebra map. The literal OpenJ model specialization is unconditional.

`RelativeChordPoints318` uses the actual mapped literal Weierstrass model and the already bound Scheme-point equivalence. For every field-valued algebra evaluation of the actual domain, the two x coordinates are distinct because the gap is a unit. Its slope equals Mathlib's actual slope (including the sign convention), and the output is exactly Mathlib Point.add of the two input points. Point membership/nonsingularity is derived from the literal model's elliptic discriminant, not assumed.

Strict replay and exhaustive recursive audit passed 59 declarations across three modules, with standard axioms only. Replay: `bash run.sh`.

Remaining boundary: tangent/equal-x and infinity branches, extension across their complement, a global relative group-scheme law, relative torsion schemes and the specified arithmetic modular-family interpretation are not claimed. This is the genuine ordinary-chord open morphism and its exact point interpretation.
