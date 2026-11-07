# Actual affine extension of the source section pair

The three public theorems in one module (12 declarations including the local
case inductive type) construct a unique actual pair of affine-ring coefficients
from local geometric data at all actual height-one prime localizations.

`LocalData` is a disjunction of concrete cases, with no supplied section
regularity/integrality premise:

- reduced vertical DVR, rational-prime uniformizer, and a genuine relative
  derivation preserving the local ring;
- ordinary horizontal Q-local ring with actual residue separation and unit
  differential coefficient;
- finite horizontal branch `t−a=u*z²`, or infinity `1/t=u*z²`, with u a unit,
  z nonzero in the maximal ideal, a unit dz coefficient and integral
  preservation by the derivation.

The last two cases deliberately allow a ramification unit. Exact square
coordinates may not exist in the original height-one localization. The
unit-twisted producer works in that original ring without adjoining a root.

`LocalData.integral` invokes the actual local proofs. `affine_sections` then
uses the actual embedded prime localizations and the proved Noetherian UFD
codimension-one intersection theorem to produce coefficients in the original
affine ring. `affine_sections_unique` proves uniqueness in its actual fraction
field. The outputs are the literal J²-scaled source section0 and section1.

## Explicit remaining realization

The actual source regular affine charts and differential trivializations must
be supplied, including their UFD/Noetherian structures and classification of
all height-one localizations by these concrete cases. Their existence is not
asserted by the type `LocalData`. Compatibility with the actual global
bicanonical line bundle, overlap transition functions and stack descent are
separate. This is genuine gluing inside one realized affine frame, not a
formalization of a global arithmetic surface or of general normal-domain
Hartogs extension.

Run `bash verify.sh` with project Lean4.35.0 and Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679. The source and recursive audit use
strict kernel checking and only the three standard axioms. No repository/Git
or frozen dependency files were changed.
