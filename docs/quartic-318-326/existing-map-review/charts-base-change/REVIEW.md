# Retrospective review of our chart, base-change and negation maps

Target: doublemover/diophantine-z-q at dea5d91b63e43d5f3ba9874c64463a0f28ff934b. Reviewer: /root/restart_checkpoint, an internal model worker. This is a bounded source/application review, not fresh compilation or acceptance of the full Diophantine theorem.

## Decision and independence

No analogue of the Baba–Granath degree-four-map mistake was found in the inspected maps. Accept the specified chart/base-change/negation isomorphisms and categorical transports at their actual hypotheses. The local additions are morphisms on their stated domains, not isomorphisms, and must not be promoted to a completed global group law.

The reviewer authored GenericFiniteCover318 and worked on proper/global-functions integration. Neither is independently accepted here. The nineteen inspected map modules were produced by other workers. This is not independent re-proving of every transitive dependency.

## Actual witnesses

1. WeierstrassOverlap318.overlapEquiv uses AlgEquiv.ofAlgHom, with actual localized coordinate substitutions and BOTH algebra-homomorphism composition identities inverse_left/inverse_right. The finite chart inverts y and the infinity chart inverts z. Equalities are on full coordinate rings, not only function fields or field points. Arbitrary commutative base rings are allowed. This is only an isomorphism of the specified opens, not the full two charts.

2. WeierstrassGluing318 constructs the actual open pushout with compatible base maps. GenericOpenPushout318.square uses the open-immersion pullback criterion and the exact range/preimage identity. The point-colimit calculation establishes that criterion; it does not infer a general scheme isomorphism from a bijection. WeierstrassChartPullback318.overlapIso is the canonical isomorphism between two objects with the same categorical pullback property. Its arbitrary-Scheme lift has both projection equations.

3. AffineBaseChange318 and InfinityBaseChange318 construct both actual tensor-algebra maps and both compositions on quotient generators and coefficients. AffineSchemeBaseChange318 and WeierstrassBaseChange318 transport these through Spec and categorical pullbacks. The latter schemeIso comes from coefficient_base_pullback, detected on both open charts, with exact base and curve projections. The scope is any commutative R-algebra S; no hidden flatness or field-point sufficiency is used.

4. ChartNegation318 proves the actual finite (x,y) to (x,-y) and infinity (x,z) to (-x,-z) maps, their square identities, and compatibility with the nontrivial chart transition. GluedNegation318.negationIso has the SAME actual global morphism for hom and inv; negation_twice is proved by pushout hom_ext. Both inverse laws therefore concern the specified map, including in characteristic two. This is not a proof of the group-inverse axiom for an unfinished global multiplication.

5. GenericProductCover318 is built from successive categorical pullback covers with both projection identities. WeierstrassTwoChartCover318 gives the actual two-chart cover and four product opens. CompletedAdditionCharts318.chartProductIso is pullback.congrHom applied to exact base-arrow equalities, and localAddition transports the existing local laws along that specific isomorphism. No cardinality or field-point correspondence substitutes for a pullback.

6. FiniteAdditionGluing318.coordinate_compatibility checks actual categorical intersections through tensor-product pullback isomorphisms. coordinateAddition is the open-cover glued morphism, with actual restrictions and base equality. FinitePairSwap318.swap is the tensor commutation equivalence. FiniteProductSymmetry318.transport_swap identifies its Spec map with actual pullback symmetry by BOTH projections. addition_commutative is literal Scheme equality under the explicit unit-discriminant hypothesis, not just a statement on points.

7. FiniteInfinitySymmetry318 and BothInfinitySymmetry318 compare actual maps over arbitrary commutative target algebras. Cancellation uses only units proved in the localized output rings. Generator extensionality gives full algebra-map equality before Spec equality. SchemeAffineTestExt318.hom_ext quantifies over ALL commutative rings and affine test maps and concludes by the actual affine open cover. This retains nilpotent directions and does not replace tests with algebraically closed field points.

## Prose and remaining scope

The inspected recovered-chart-intersections, relative-product-cover and relative-whole-infinity READMEs explicitly leave global four-chart compatibility/gluing and group axioms open. CompletedAdditionCharts318 likewise separates transported local maps from later compatibility. No corrective mathematical edit is requested in this lane.

Contact and Hodge separately found a frozen character-packet README calling root-sign automorphisms “inertia flips.” That is outside the accepted maps here. The active reading must say root-sign flips and retain the missing valuation-theoretic identification. Preserve the old hash-bound producer artifact and attach a visible correction rather than silently changing historical evidence.

## Nine review obligations

- Claim/object: the named coordinate rings, localizations, glued curve and actual relative products.
- Source/version: exact file hashes in receipt.json, with pinned Mathlib constructions retained as dependencies.
- Hypotheses: arbitrary commutative rings where stated; unit discriminant for addition coverage; explicit localized units for cancellation.
- Construction/comparison: actual maps, two-sided inverse laws or categorical universal properties, and projection/base equations identified above.
- Quantifiers: full ring equalities and arbitrary affine/Scheme tests, including nonreduced tests.
- Consumer: transport of local laws and symmetry, not a global group scheme or multiplication kernel.
- Provenance: non-author source review of the listed maps; authored generic finite-cover and proper/global-functions proofs excluded.
- Adverse findings: no analogous invertibility defect in this bounded read; the separate sign/inertia prose mismatch retained.
- Execution/closure: no new Lean run; this does not establish all 1083 modules mathematically complete, PEL realization, or unconditional sourceArithmetic.

Hosted run42450454824 at0e5ff6ec3af901673ae4cf312329f3da0e503cf4 passed all50 jobs, including Full progress axiom audit job128640564405. Reviewed source bytes are unchanged through dea5d91. This is dependency-aware cached verification plus a complete recursive audit, not a from-scratch clean rebuild.
