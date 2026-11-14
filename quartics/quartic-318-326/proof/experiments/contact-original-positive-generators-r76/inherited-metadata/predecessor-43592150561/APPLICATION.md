# Exact original cohomology-coordinate application repair

## Observed evidence and narrow delta
Run 43586414080 at f89bd0a3cb8a788d6c7f2f494a21d7d103a893cb, positive r74 own artifact 14110484994. OriginalLineRationalCohomology318 passed 28.790 seconds; ContactOriginalCohomologyCoordinates318 failed 31.948 seconds. The two remaining restriction goals compare `(coordinates c L).toAddEquiv x` with `(coordinates c L) x`. The third hard error is failure to synthesize IsIntegral of the actual Contact model at the existing boundary-surjectivity theorem application.

The candidate adds only LinearEquiv.coe_toAddEquiv to the two existing `simp only` lists and explicitly installs ContactProjectiveModel318.model_integral c inside the boundary_surjective proof. Pinned Mathlib Algebra/Module/Equiv/Defs.lean at 56a005855ea17e0b0958f73ec801ae140b0a1679 states coe_toAddEquiv by rfl. This identifies the same function after forgetting linear structure; it changes no coordinate map. The unused-simp warnings are not additional hard errors.

## Required inputs and actual objects
For every c : Fin 4 → Qˣ and EVERY line L on ContactProjectiveModel318.model c, the full finite and infinity chart opens and their original intersection are unchanged. overlapCoordinates remains exactly `(overlapEquiv c L).symm.trans (coordinates c L).toAddEquiv`. coordinates is the actual finite Laurent-module recovery composed with the original finite basis base-change coordinates, not an arbitrary equivalence or dimension-selected map.

finite_res and infinity_res continue to consume the existing full-open square at `(finiteSectionsEquiv c L).symm s` or `(infinitySectionsEquiv c L).symm s`. The existing inverse cancellation and same whole-overlap equality transport are untouched. The only residual conversion is from the linear equivalence's additive coercion to its identical function, with no scalar change. All sections of both opens are covered, not a finite generating set or generic fiber.

## Exact surjectivity application and maps
OriginalLineMayerVietorisQuotient318.boundary_surjective requires an integral ambient scheme, the actual original line, two affine opens, and the full cover equality. The model_integral c theorem proves IsIntegral of the literal normalization `(coverMap c).normalization` using the actual OpenOrder domain and cover; it is not merely IsIntegralHom of modelMap. The candidate supplies that exact already-proved instance locally. finite_affine c, infinity_affine c and cover c remain the original arguments. No new theorem premise is introduced.

coordinateBoundary is still the original derived Mayer–Vietoris boundary precomposed with the inverse of the same overlapCoordinates. boundaryLinear is still its exact toRatLinearMap. The target H1 is actual Sheaf.H of the original additive line in degree one, with rational action from OriginalLineRationalCohomology318.cohomologyModule at ContactIntrinsicDifferentials318.structureMap c. Surjectivity is the original boundary surjection composed with this exact inverse-coordinate surjection. No quotient/surrogate replaces the target, no signs or normalization factors change, and boundary_original stays byte-identical on every full overlap section.

## Consumers, domains and exclusions
ContactOriginalLaurentBoundary318.zero_iff consumes finite_res/infinity_res to compare the SAME derived-boundary kernel with the difference of original restrictions, including its minus sign. ContactOriginalLineSectionsFinite318.finite_formula/infinity_formula consume the same two equalities for full global sections. ContactOriginalLineHOneFinite318.equivalence directly consumes boundary_surjective c L in `(boundaryLinear c L).quotKerEquivOfSurjective`; it retains the same kernel equality, quotient and original H1. Complete primary consumer files are retained.

All c of units and all original lines/sections remain; no extra nonzero-section, rank, triviality, generic/nonempty-open, affine-ambient or point hypothesis is added. All definitions and public theorem statements are unchanged. No imports, resource options, admission or trust setting changes. Only this canonical source will change in the unchanged 107-module ordered closure; the other 106 sources remain byte-identical. Existing downstream compilation risks are not repaired speculatively.

## Verification boundary
This is a source-level bounded candidate, not a Lean pass. No local Lean/Lake/compiler, kernel or recursive-axiom check has run. Independent source review and packet-specific propagation review are separate. Historical verdicts are not promoted to current mathematical acceptance.
