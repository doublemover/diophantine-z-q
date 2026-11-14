# Independent source review: whole original affine-chart smoothness

Scope: run 43539970197, published head 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b. Source/provenance review only, no local Lean/Lake/compiler run. No source blocker found. Candidate elaboration and kernel acceptance remain unverified until hosted replay.

## Exact bindings

- FourRootAffineSmooth318 before: 3e79ed68cbedb50021e9681ccea7a6d8b9bfcd63c10907bc1e0f99a2555281da
- Final candidate: 6f858b62cd64dd7cd19a8531e2922661e00d5424ba125030dfc58cf0b92ae86c
- AFFINE-SMOOTH-APPLICATION.md: 273558dee7ec401c561dfa8a2a756ab314118d640a799b4a7f7903f2334b0034
- Exact zero-r34 log: 97a11c3108aca20fc15d83f771830303aabc295f4dc769314779ac3408bc6816
- Own RESULT: 0af6d8cf673c0645ebc93491a3d21335ad328ae34abb1982ac06d6c5a1a03579
- Published zero-r34 intake: 30e545a8d8c4a39a24d43bb69c219f70a9f4fcc4aee0f85504cc65b5139c6b5d

Before bytes and RESULT packet hash independently match the actual published predecessor. Its GenericField module passed 3.170 s; Smooth failed 3.770 s. Those are historical module results, not acceptance of this changed source. Exact diagnostics identify the four residual determinant normalizations, missing hb and omitted dependent theorem arguments, and empty-product prime nonmembership.

## Native map and determinant

Pinned Submersive.lean jacobiMatrix_naive has row i = chosen derivative variable and column j = equation j. The candidate hmatrix preserves that orientation literally. jacobian_eq_jacobiMatrix_det applies the presentation polynomial algebraMap to this determinant. Generators.naive explicitly installs the native quotient algebra using inferInstance; Presentation.naive and PreSubmersivePresentation.naive retain it. Thus the subsequent change to Ideal.Quotient.mk of the SAME ideal span(range(equation b)) is the native quotient map, not a substituted evaluation map or additional compatibility premise. The kernel must still check this definitional normalization in the candidate.

The twelve-entry Fin4-by-Fin3 succAbove table retains the complete complement of each branch index, in order. Its proof is decide, not native_decide or an axiom. It is used only for finite index normalization. Independent exact symbolic permutation expansion confirms each chosen Jacobian has coefficient -8 multiplying exactly the three non-omitted roots: the omitted row differentiates every equation by t and is -1, while each other row has its single 2*z_k diagonal entry. This source check is not a Lean proof. No sign, square, branch or factor is removed.

## Domain, binders and actual consumer

The added explicit hb:Function.Injective b binds distinct_roots_not_both, jacobian_span, smooth and integrallyClosed to their originally intended section input. Their failed predecessor did not retain that binder, so literal public-header equality is intentionally not asserted. This is the distinctness needed to exclude simultaneous roots; it is not an extra premise on an already valid general smoothness theorem. The unchanged callers in FourRootInfinitySmooth318, FourRootWholeSchemeGeometry318, FourRootActualOrderGalois318 and FourRootActualFrameDenominatorCover318 already pass b,hb. jacobian_formula, scalar_not_mem and branch_minor_not_mem remain hb-free.

The empty-product case now introduces its existing implication premise and obtains 1 not in the prime from scalar_not_mem at complex 1, normalized by map_one. It adds no assertion beyond the prime's existing properness and unit exclusion. The induction still covers arbitrary finite subsets and the full Fin3 product.

The branch cover still quantifies all prime points of the full original affine quotient. If one root lies in a prime, distinctness excludes every other root and supplies its complementary minor; if none do, branch 0 supplies a minor. The same full span-to-top argument feeds actual Jacobian local smoothness, then actual domain normality. No unramified-only locus, radical quotient, separate field component, selected point family or replacement chart is introduced. Imports, resource/trust options and the final ring and scalar maps are unchanged.

## Primary evidence

Pinned Mathlib source read:
- Extension/Generators.lean: 73668592d92a264ffb080842b17f34fff703a7e64dfd34374351df2b8f254177
- Extension/Presentation/Basic.lean: 30f9c13895e434c00499f4c4024f9fb9630107fd481e2b3d6e7e84ed5586227d
- Extension/Presentation/Submersive.lean: ff90d9b4ca6421668326f1fff8b6a84da9ff28d7e0062022210d27a38a10e243

Successor propagation and complete packet source sets require a separate review. No independent mathematical acceptance is granted by this report.
