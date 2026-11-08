# Bounded independent review: actual finite-chart and product schematic density

## Decision and authorship

Accepted within the exact source scope bound in `acceptance.json`: the four-module finite-chart packet and three-module finite-product packet establish **schematic**, not merely topological, density and the stated separated-target equality extensions. The arbitrary-base claims retain nilpotents. No reducedness or field-point substitution is hidden in these proofs.

The reviewer did not author the seven producer implementations. The reviewer coordinated the desired interfaces and authored their global unit/inverse/commutativity consumers. Accordingly this is a non-author acceptance of the density producers and their applicability to the stated objects, not independent acceptance of the reviewer's own downstream group-law proofs. Existing infinity-ring presentations, gluing/cover identities, smoothness/properness and Mathlib categorical infrastructure remain retained predecessors rather than a newly audited full dependency closure.

All seven sources, both READMEs and the relevant pinned Mathlib schematic-dominance implementation were read. No replay was performed. The receipts' strict compiler/recursive-audit results are separately identified evidence.

## 1. Actual infinity denominator and schematic density

`InfinityMonicPresentation318` uses the literal infinity equation
z − x³ − A x z² − B z³ = 0.
Its auxiliary algebra is the monic cubic quotient over R[z]. Both actual algebra maps are constructed and `backward_forward` is proved. Only injectivity of `forward` is used. A one-sided inverse is **not** mistaken for an isomorphism.

The auxiliary monic quotient is free, hence flat, over R[z]. The polynomial variable z is a non-zero-divisor over every coefficient ring. Flatness preserves its regular action; injectivity of `forward` transfers regularity to the actual infinity ring. This proves exactly the denominator needed for the original overlap localization. There is no domain or reducedness assumption.

`SpecSchematicDensity318.spec_of_injective` transports injectivity through the actual Gamma–Spec isomorphisms and proves the morphism's ideal-sheaf kernel is zero. It does not infer schematic dominance from topological dominance. This distinction matters over nonreduced bases.

`FiniteChartSchematicDensity318` obtains injectivity of the original infinity-overlap localization from that regularity. It uses the actual pushout overlap identity to compare the finite-chart and infinity-chart kernels, then the actual two-chart open cover to prove the finite chart's kernel is zero globally. Neither a smaller coordinate open nor only the generic fiber is substituted for the complete curve.

## 2. Equality extension is valid without reducedness

`SchematicEqualityExtension318.ext` first uses the supplied equal structural composites to regard both maps as morphisms over the same base. Their actual equalizer is a closed immersion because the relative target is separated. The given schematically dominant map factors through that equalizer. Therefore the equalizer's ideal kernel is contained in the zero kernel of the given map. A closed immersion with zero ideal kernel is an isomorphism, so its equalizer equation gives equality of the two original maps.

This is an ideal-kernel argument on the actual Scheme maps, not equality on points. It retains infinitesimal directions. The concrete `hom_ext_to_completed` uses the previously proved properness of the actual target cubic for separation. The source and target coefficient pairs remain distinct parameters. No source or target unit-discriminant premise is added to the single-chart endpoint.

## 3. Product stability has the required hypotheses

`FiniteChartQuasiCompact318` separately proves quasi-compactness of the actual finite-chart inclusion. Its composite with the completed structure map is the actual affine structure map; the completed structure map is separated via properness. Thus the cancellation step for quasi-compactness has its required hypothesis, even over a non-Noetherian coefficient ring.

`SchematicProductDensity318.leftMap`, `rightMap` and `productMap` are explicit pullback constructions. Their two projection equations identify the exact maps. The use of schematic density under flat base change requires both quasi-compactness of the dense map and flatness of the base-change map. These are supplied, not omitted. The product construction uses the openness of the left chart to make its structural composite flat; the right chart's actual instance is also open in the intended application.

The pinned Mathlib `SchemeTheoreticallyDominant.lean` definition is kernel-zero. Its `pullbackSnd`/`pullbackFst` instances explicitly require quasi-compactness and flatness, and their proof uses injectivity of the relevant ring map after flat tensor/base change. The producer does not call the separate topological-density equivalence that requires a reduced target.

## 4. Exact pair and left-associated triple

`FiniteProductSchematicDensity318.pairMap` starts with the literal pullback of the two affine Weierstrass structural morphisms and lands in the literal completed relative square. The `pullback.congrHom` transport uses the proved finite-chart structural identities. `pairMap_fst` and `pairMap_snd` identify both actual coordinates.

`tripleMap` has exactly the requested left-associated source and target, namely pullback of the pair structural map with the curve structural map. `tripleMap_fst`, `tripleMap_snd` and `pairMap_structure` retain that bracketing and all structural maps. It is not merely an unspecified isomorphic cube.

For pair/cube density the unit-discriminant hypothesis supplies actual smoothness, hence flatness, of the completed curve and then of the pair structural morphism. No field, domain, reducedness, characteristic-zero or invertibility-of-3 hypothesis is used. The resulting equality-extension endpoints retain the equal-base-composite premise and the exact finite-product restriction.

## 5. Concrete consumer comparison and limitations

The unit/inverse consumer's source is the same actual completed curve, and its restricted map is the original finite chart. Its desired target is the same completed curve; its explicit structural-composite identities satisfy the single-chart equality-extension premise.

For commutativity, `CompletedAdditionCommutative318.inputChart_eq_pairMap` compares the finite input chart of the actual globally glued addition with this exact `pairMap` by both pullback projections. Thus the pair endpoint is suitable for that consumer. This statement records the actual source-level map comparison, not independent approval of the reviewer-authored consumer.

The literal associativity route currently uses a separately proved reduced triple source and residue-field tests. The product-density packet does not itself prove associativity, any group axiom, a group object, or a multiplication kernel. Those remain separate consumers. The literal Scheme-map equality, once proved, will apply on arbitrary test schemes over its literal base; this is distinct from proving associativity over every arbitrary coefficient ring.

## Evidence boundary

The exact accepted receipts are:
- finite-chart-density: d7450bf2176e40856b927e748436d825b509811296c379fd82bb495f8566ee55.
- finite-product-density: 6b59c0dc2ac66cf35fb57c19378f287ff3fc8ba5c20b5276e00391ce5153fb08.

`acceptance.json` binds all seven implementation source hashes, both prose summaries and the inspected Mathlib file. Hash identity checks are not mathematical certification by themselves; the source assessment above is the independent judgment. Hosted joined integration remains separate, and this review does not rewrite either producer receipt.
