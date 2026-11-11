# Cotangent frame simplification repair

This is a narrow successor to frozen `pel-original-zero-local-length-r1`. Only PolynomialRelativeCotangentFrame318.lean changes: RingHom.id_apply is added to the simp-only list at line53, resolving the identity-ring-hom wrapper exposed by hosted batch214. All other 579 Lean sources are byte-identical predecessor copies, pinned in COPY_BINDINGS.json. Statements, hypotheses, maps, scalar structures, ideals and consumers do not change. Prior review is historical; independent review and hosted checking of this successor remain pending. No local Lean build or profiling was run.

The exact diagnostic is build/ci214-cotangent/logs/PolynomialRelativeCotangentFrame318.log. This propagation prevents the same known failing source from being rescheduled in another active closure. Frozen predecessor files are untouched. The mathematical scope and limitations in the historical description below remain unchanged.

## Historical predecessor description

# Original local zero-quotient lengths

Reconstruction from exact remote r112 at 31a0e67e on 2026-11-11, not a recovery or acceptance of unavailable remembered packet 847.

Three new sources compare the actual localizations of the previously constructed whole derivative-zero ideals with the independently trace-defined different ideals. At every original finite branch point and all eight original infinity centers, that local ideal is the actual local ring's maximal ideal. At every other finite complex point it is the whole ring. Consequently the actual local quotient rings are reduced, and their actual module lengths are one or zero, respectively.

The original completed PEL-to-contact point map then pulls these module lengths back to the SAME original source points. Their equality with the independently computed trace-different coefficients is a theorem, not a definition. Summation over the forty original ramification points is forty. The infinity calculation retains the reciprocal projective base v=u².

This is a result about actual localized quotient rings/modules at all the specified complex points. It does NOT yet identify them with the intrinsic relative-cotangent SHEAF stalks, prove reducedness at every scheme prime, construct a global sheaf cokernel equivalence, or prove a global coherent-sheaf length theorem. Those joins remain open and must not be inferred from point support or the integer forty.

The dependency closure contains 580 modules: 577 byte-identical r112 sources and three new modules. Existing reviewed/hosted status is not promoted. Static dependency checks are separate from hosted Lean elaboration/kernel verification and independent source review, both pending. No local Lean builds or profiling were performed.

Primary pinned mathlib inputs read: RingTheory/DiscreteValuationRing/Basic.lean, irreducible_iff_uniformizer, Irreducible.maximalIdeal_eq and length_quotient_pow_maximalIdeal; RingTheory/Length.lean, Module.length and length_eq_zero. Commit 56a005855ea17e0b0958f73ec801ae140b0a1679. The length theorem receives the actual local ring with its previously constructed DVR instance and exponent one.
