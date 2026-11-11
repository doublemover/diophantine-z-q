# Cotangent frame simplification repair

This is a narrow successor to frozen `pel-original-zero-scheme-reduced-r1`. Only PolynomialRelativeCotangentFrame318.lean changes: RingHom.id_apply is added to the simp-only list at line53, resolving the identity-ring-hom wrapper exposed by hosted batch214. All other 105 Lean sources are byte-identical predecessor copies, pinned in COPY_BINDINGS.json. Statements, hypotheses, maps, scalar structures, ideals and consumers do not change. Prior review is historical; independent review and hosted checking of this successor remain pending. No local Lean build or profiling was run.

The exact diagnostic is build/ci214-cotangent/logs/PolynomialRelativeCotangentFrame318.log. This propagation prevents the same known failing source from being rescheduled in another active closure. Frozen predecessor files are untouched. The mathematical scope and limitations in the historical description below remain unchanged.

## Historical predecessor description

# Actual whole derivative-zero scheme reducedness

Reconstruction from exact r112 sources at remote 31a0e67e on 2026-11-11. The missing remembered later packet is not treated as available proof or an acceptance record.

This draft extends the actual signed-root local computation to EVERY scheme prime. Any prime containing a root lies over the actual root-zero prime. The already constructed relative unramifiedness at arbitrary primes identifies the original root-generated local ideal with the actual local maximal ideal. The existing full principal-chart cover then shows that the original whole derivative-zero ideal localizes at every prime to either the unit ideal or the maximal ideal.

Localization of radicals and equality detected at all maximal ideals prove that the ORIGINAL finite ideal is radical. The genuine whole-ring reciprocal polynomial-base isomorphism transports this to the ORIGINAL infinity ideal. The two original quotient rings are therefore reduced. Their actual open immersions cover the existing glued zero scheme, so the SAME zero scheme is reduced everywhere.

No assertion that every prime is complex-valued, no Nullstellensatz shortcut, no replacement by a reduced support, and no altered zero-scheme inclusion occurs. This is not yet the global intrinsic relative-cotangent sheaf cokernel comparison or identification of its stalk lengths. No PEL or full arithmetic endpoint is claimed.

All predecessor source files are byte-identical r112 copies. Three new modules are separate from the frozen local-length and affine-cotangent packets, so this reconstruction does not depend on unreviewed conclusions from them. Hosted Lean and independent review remain pending; static source/dependency checks are not kernel acceptance. No local Lean builds, replay or profiling ran.

Primary pinned mathlib sources read: RingTheory/Localization/Ideal.lean (IsLocalization.map_radical), RingTheory/Ideal/Maps.lean (IsRadical.comap and comap_map_of_bijective), RingTheory/Ideal/Operations.lean (radical_eq_iff and prime radicality), AlgebraicGeometry/Properties.lean (IsReduced.of_openCover). Pin 56a005855ea17e0b0958f73ec801ae140b0a1679. Original actual unramified local maximal-ideal application was compared to FourRootActualLocalUniformizer318 and the all-prime producer FourRootAllPrimeRelativeDifferent318 before extending its domain.
