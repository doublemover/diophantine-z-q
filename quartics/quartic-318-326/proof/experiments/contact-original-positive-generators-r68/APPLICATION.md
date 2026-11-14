# Original whole-open square proof composition (source-only)

Exact basis: hosted run 43539970197 at 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b, positive predecessor contact-original-positive-generators-r67, artifact 14091631964. OriginalTensorChartWholeRestriction318 passed (24.979 s); ContactOriginalWholeRestriction318 failed (66.475 s). The only reported errors are rewrite failures at lines 83 and 93. Earlier explicit original chart specializations and the generic image_restriction helper report no error, but the whole module has not passed.

Before SHA-256 619d6667786ed04c54d15216d55c7e013e7f3e8250291343a3db5561d80984d8. Candidate SHA-256 7703c3170db29686170082260f439fcea1f3dbed7724381399380a643bd888cd. Exact own log/RESULT, before/after and diff retained. Only finite_square and infinity_square proof bodies change. Imports, definitions, public declarations, all preceding proof bodies and resource bounds remain unchanged.

## Observed failure and revised route

The former dsimp-only step unfolds overlapEquiv but leaves AddEquiv.trans applied as a whole. Consequently rw cannot find overlapSectionsEquiv applied to finiteDirect/infinityDirect. The diagnostic explains that under implicit transparency the common ModuleCat carrier's additive structure is not recognized as the definitionally equal original Γ carrier. The repair does not change either carrier or introduce a replacement equivalence. It avoids rewriting within the partially unfolded term entirely.

For each side, first lift the existing ContactWholeOpenSectionRestriction318 finite_square/infinity_square equality with congrArg of the fixed original mapIso(eqToIso(overlap_image c).symm).op additive equivalence. Its argument s is explicitly typed Γ(L.object,(into c) ''ᵁ ⊤), the actual original image-section module. This local equality is named hs. Separately, congrArg (overlapEquiv c L) of the unchanged finite_direct/infinity_direct identifies the tensor-recovered section with the same direct original section. Compose that equality with hs and the unchanged image_restriction result. The overlapEquiv endpoint is definitionally the original trans evaluation, rather than being rewritten at implicit transparency.

## Required inputs and actual construction

Every c:Fin4→ℚˣ, every original global line L, and every full-open finite/infinity section m is retained. finite_direct/infinity_direct are the unchanged explicit applications of OriginalTensorChartWholeRestriction318.original_restriction. Their coefficient rings, original finite/infinity algebras, reciprocal u↦T⁻¹ action, projection/edges, inverse tensor charts, inv_base/inv_chart equalities, original line and comparison isomorphisms are untouched. No new hypotheses, source choices or excluded cases occur.

The lifted source equality has left side overlapSectionsEquiv c L (finiteDirect/infinityDirect c L m), right side the original L.object.presheaf restriction from the full chart image to (into c) ''ᵁ ⊤, applied to the existing chart sections equivalence. Its entire section domain is covered, not a set of generators. The fixed target equivalence maps this image open to finiteOpen c ⊓ infinityOpen c, using exactly overlap_image c in the same h.symm/op direction as overlapEquiv.

The generic image_restriction helper still takes the same equality U=V, original U≤W inclusion, same target inf_le_left/inf_le_right and exact source section finiteSectionsEquiv/infinitySectionsEquiv c L m. Its conclusion is restriction W→V of that very section. The resulting value is a section of the SAME original global L on the full original intersection. No rationalized object, changed scalar action, smaller open, new pullback identification or surrogate class is substituted.

## Consumers and limits

The public finite_square/infinity_square statements are byte-identical and remain the inputs to downstream original cohomology and positive-twist constructions. The 107-module closure is unchanged; the other 106 source files are byte-identical. No resource option is raised or disabled. The old source review is historical only; this changed equality-composition route requires new distinct internal source review and separately reviewed propagation.

No local Lean or Lake run, kernel acceptance, recursive axiom validation, or full arithmetic theorem claim. In particular exact elaboration of the final definitionally equal trans endpoint remains a hosted verification question; the term proof is a bounded candidate, not a claimed pass.
