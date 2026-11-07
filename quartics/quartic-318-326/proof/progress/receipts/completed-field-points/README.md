# Completed literal Weierstrass field points

This packet identifies the actual base-preserving field-valued points of the completed two-chart Weierstrass Scheme with the genuine Mathlib Weierstrass point type, including infinity. It consumes the actual Scheme and chart maps, not an assumed field-point classification.

## Checked construction

`CompletedFieldPoints318` works over any commutative base ring R and any field K equipped with an R-algebra structure. A genuine morphism `Spec K` to the completed scheme factors through one of the two actual open charts because `Spec K` has one underlying point. In the infinity chart, the image of z is either nonzero, in which case the actual localization factors the point through the finite overlap, or zero. If z=0, the actual equation gives x³=0, hence x=0 in K; the quotient universal property then identifies the morphism with the actual infinity section. The infinity section has empty inverse image in the finite chart, so the resulting alternatives are disjoint.

The result is the explicit equivalence

`completedEquiv A B : SchemePoints A B ≃ Option (AffineSchemeSolutions318.SchemePoints A B)`.

Its inverse sends `none` to the actual infinity section after base change and `some p` to the actual finite-chart inclusion. Both coordinate and infinity evaluation laws are checked.

`LiteralCompletedPoints318.fieldPointEquiv` composes this actual classification with the separately checked finite-coordinate equivalence. It identifies all actual points of the completed literal OpenJ family over K with `(LiteralWeierstrassPoints318.model N).Point`. Its infinity point is exactly `Point.zero`; finite points retain their actual x,y coordinates. The literal discriminant unit supplies nonsingularity; no extra nonsingularity or field-point-equivalence premise is assumed.

## Reproduction and boundary

Run `bash completed-field-points/build.sh`. The script explicitly lists all dependency directories, rebuilds both modules with `debug.skipKernelTC=false`, and recursively audits every declaration against the three standard Lean axioms. Sources and log hashes are recorded in `receipt.json` and `SHA256SUMS`.

This is an exact field-point interpretation of the actual completed Scheme. A global coefficient-base-change isomorphism, relative group law, relative torsion scheme and remaining global refined geometric realization are separate tasks. This packet does not infer a group-scheme law merely from a bijection of field-valued points.
