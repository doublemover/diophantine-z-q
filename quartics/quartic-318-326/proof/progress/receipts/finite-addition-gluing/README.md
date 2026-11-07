# Actual finite-input addition morphism by four-chart gluing

This packet constructs an actual Scheme morphism from the whole relative product of two finite short-Weierstrass inputs to the completed cubic. It assumes only that the actual discriminant is a unit; the literal OpenJ specialization is unconditional.

`FiniteAdditionLocal318.local_agreement` assembles all six checked cross-chart identities and diagonal uniqueness into compatibility over every common coefficient algebra. The diagonal case uses the genuine localization universal property. The common algebra for each categorical overlap is the actual tensor product of the two localization rings over the original pair algebra; its two maps agree on every input-pair element.

`FiniteAdditionGluing318.coordinate_compatibility` transports these algebra identities through the actual `pullbackSpecIso` to prove equality on the genuine categorical pullbacks. `coordinateAddition` then applies actual `Scheme.OpenCover.glueMorphisms` to the four-chart cover proved in `finite-pair-cover`. `addition` transports the result to the actual relative self-fiber-product of the finite input scheme. `restriction` proves all four original chart morphisms are recovered exactly. The resulting map preserves the original base.

This proof does not use equality on field points, reducedness, density, or an assumed morphism-extension theorem to infer chart compatibility. Nilpotent coefficient directions are included by the arbitrary-ring algebra identities.

Run `bash build.sh` for a fresh strict kernel replay and recursive axiom audit. Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The sibling dependencies and their frozen cross-chart proofs are listed in `run-one.sh`.

Boundary: both inputs are in the finite chart. Input-at-infinity extension, a complete group-scheme law and its axioms, multiplication/primitive-torsion geometry, and the full refined global realization remain separate. No final unconditional Diophantine endpoint is claimed.
