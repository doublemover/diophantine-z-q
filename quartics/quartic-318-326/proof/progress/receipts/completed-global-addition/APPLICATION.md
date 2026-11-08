# Global addition application contract (author's source check)

Status: author application record for the completed global-addition packet. Per-source strict development checks and a recursive axiom audit are recorded in the receipt once frozen; hosted integration and independent review remain separate. This is not an independent acceptance record and does not certify the full group axioms.

## Required and constructed inputs

The downstream construction is `CompletedAddition318.addition A B hD` on the literal pullback of `WeierstrassGluing318.structureMap A B` with itself. The base is an arbitrary commutative ring R, A and B lie in R, and hD states that -16(4A^3+27B^2) is a unit. No reducedness, field assumption, or invertibility of 3 is added.

`Scheme.OpenCover.glueMorphisms` requires a map for every index of the selected open cover and equality on every pairwise pullback intersection. The constructed cover is exactly `WeierstrassTwoChartCover318.productCover A B`, indexed by Fin 2 × Fin 2. All four indices (finite,finite), (finite,infinity), (infinity,finite), and (infinity,infinity) occur in `CompletedAdditionCharts318.chartAddition`. No denominator-only subcover or geometric-point subset replaces this domain.

## Comparison maps and coverage

Each cover component is transported by `chartProductIso` to the pullback of the two literal chart structure maps. `chartProductIso_fst` and `_snd` identify both projections. `first_input` and `second_input` then identify the projected completed-curve inputs with the actual product-cover inclusion followed by the global product projection.

`AlgebraChartCompatibility318.evaluate_congr` treats all four input-chart combinations over every commutative R-algebra S, including nilpotents. Its finite/infinity transitions use the actual categorical chart intersection from `WeierstrassChartPullback318.square`, not a comparison on field points. `ChartInputEquality318.finite_infinity` obtains the literal coordinate relations from an actual overlap ring homomorphism. `WholeBothNaturality318` restricts the whole infinity-input law using the actual localization maps. The finite swap map supplies the precise order reversal for the finite/infinity chart.

`AffineProductEvaluation318.product_iso` identifies the actual tensor-product affine isomorphism on both projections with the literal tensor pair of algebra maps. `ChartPointEvaluation318.evaluation` therefore compares each actual chart addition, not merely a related coordinate function, with `evaluate`.

For an arbitrary affine Scheme test object, `ChartSchemeCompatibility318.affine_agreement` induces its R-algebra structure from its actual common map to Spec R. Thus the quantifier covers all affine test maps, not only those already carrying a chosen compatible algebra structure. `SchemeAffineTestExt318.hom_ext` extends this equality to every Scheme test object. The constructed test object in `local_compatibility` is precisely the whole pullback intersection of two selected cover components. The two input equalities follow from its literal pullback condition.

## Identity of the consumed object

`CompletedAddition318.addition` is the map returned by `productCover.glueMorphisms` from those actual local maps and full intersection equalities. `restriction` proves its restriction to each cover component is the selected local addition. `addition_over_base` proves that its target structural composite is the product structural map. `CompletedAdditionRestrictions318.inputChart` is the inverse transport followed by the exact cover inclusion; its projection lemmas and `inputChart_addition` identify the map consumed by later inverse, unit, point-reading, and associativity arguments.

This packet establishes an actual global Scheme morphism with its chart restrictions only after verification. It does not by itself establish associativity, identity, inverse, group-object packaging, or multiplication-by-three. Later drafts must be reviewed and checked separately. In particular, a proposed residue-field argument for associativity is restricted to the literal reduced family, not arbitrary nonreduced coefficient rings.

## Historical scope

The five reconstructed intersection/naturality sources were checked before the cloud reset, but old logs and receipts are not used as evidence for the reconstructed bytes. They received a fresh five-module replay and recursive axiom audit, and are now published predecessors. The subsequent gluing route has its own per-source strict development checks and recursive audit recorded here; hosted integration and independent application review remain pending. This document is an author's source comparison; a separate reviewer must record any independent acceptance without attributing all-predecessor review to this bounded inspection.

## Iterated operations and actual associativity domain

`CompletedIteratedAddition318.doubling` is the actual diagonal followed by the glued addition. `tripling` is its actual pair with the identity, followed by the same addition. Both structural composites are proved. Their interpretation as group multiplication and any kernel claim are not asserted by their definitions.

`CompletedAdditionTriple318.triple` is exactly the left-associated pullback of the actual pair structural map with the curve structural map. `first`, `second`, `third`, `pair12` and `pair23` have their literal projection/base identities. `leftAssociate` and `rightAssociate` are actual composite morphisms on this same triple source, with equal structural composites. This packet does not assert their equality. That remaining equation requires a separate proof.
