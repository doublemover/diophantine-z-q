# Actual finite-product schematic density

Status: three producer modules strictly checked with debug.skipKernelTC=false; recursive import-all audit passed 68 declarations, including private/generated declarations. Hosted integration and independent source review are pending. No full dependency rebuild was run.

FiniteChartQuasiCompact318 proves the actual finite chart is quasi-compact over every commutative base, by the affine structure map and the separated completed structure map. SchematicProductDensity318 constructs actual left/right pullback maps and their product, with exact projections. Quasi-compact schematic dominance survives the required flat base changes; no reducedness or geometric-point shortcut is used.

FiniteProductSchematicDensity318 constructs the actual finite square and the left-associated finite cube inside the corresponding completed relative products. It proves both are schematically dense over an arbitrary commutative ring with unit discriminant. The unit discriminant is used through actual smoothness/flatness of the completed curve. Nilpotents in the coefficient ring are retained.

The endpoints pair_hom_ext_to_completed and triple_hom_ext_to_completed extend equality of morphisms to a separated completed cubic from equality on these exact finite product charts, provided the two maps have equal structural composites. The triple source is literally pullback (pullback.fst p p ≫ p) p. This packet does not prove associativity, commutativity, or a multiplication kernel; those are separate consumers.

Dependency: the frozen finite-chart-density packet, receipt d7450bf2176e40856b927e748436d825b509811296c379fd82bb495f8566ee55. The completed target is separated by its previously proved properness, without a target unit-discriminant hypothesis.
