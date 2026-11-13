# Independent bounded Picard source review

Reviewer: lean_review_resume (internal model review, distinct from picard_repair_resume).
Base commit: `4d85d68746c3729658dd5f85869f7dd4fc2b505f`.
Observed hosted failure: run `43344479993`.
Review scope: four draft successor changes against their retained exact first-failure logs, predecessor sources, and defining source lemmas. This is not Lean verification, independent application acceptance, or an arithmetic theorem claim. No local Lean build was run and no user computer was accessed.

## Reviewed source bindings

| Successor | Changed source | SHA-256 |
| --- | --- | --- |
| contact-relative-site-descent-r73 | ActualAffineEffectiveComparison318.lean | 81a039481c3f626cb8271e0c6ba7d1e6e2a3ac1948fe63efbcf16d4d4240da98 |
| original-five-kernel-norm-equivalence-r7 | OriginalThickenedOpenSections318.lean | d52055284d02d73c3451b2424201c4f575b50dede50c146b933b15bb1c7ae34a |
| original-finite-quotient-reconstruction-r59 | OriginalCartesianChartCoefficients318.lean | 751a8fa884465cfdaa0e3337b20392d5aa4a682a7d5138def578764153a63208 |
| relative-original-normalized-kernel-gluing-r3 | OriginalOpenPullbackSections318.lean | c8450e6421b2b752fa803891d1601da611b7d10ab8c57a3f9e86744a8e7d8573 |

Paths are under `quartics/quartic-318-326/proof/experiments/`. Independently verified exactly one changed root Lean source and no added root Lean source in each successor, and that all four after-source hashes match HOSTED-43344479993/PROVENANCE.json. Predecessor comparison was against r72, r6, r58, r2 respectively. All four exact retained failure logs and bounded patches were read.

## Application comparisons

1. **Actual affine comparison.** Read ActualAffineLineReconstruction318.line/pullbackIso, OriginalGeometricAffineLine318.line/pullbackIso/coalgebra, ReconstructedOverlapCompatibility318.descendedModule/original_overlap, SheafIsoTransport318.transport_injective/conjugation, ActualCanonicalOverlap318.transport and ActualAffineTensorTransport318.overlap. The named M is exactly the reconstructed descended module for the original tensor-transported overlap with the original diagonal/triple laws. The typed comparison retains its original pullback isomorphism; there is no alternative sheaf or freely chosen comparison. The same doubleIso inverse, first/second maps and equality paths are used. Left composition with the first pullback of e.hom converts the conjugation equation to the same commuting square without rewriting the dependent overlap input. The full faithfully-flat affine quantification and actual categorical-double overlap are preserved. Immediate consumers comparison_commutes/effective and ActualAffineDescentData318 still consume the original comparison, not a replacement datum.

2. **Thickened open sections.** Read OriginalThickenedOpen318.localBase/Local/inclusion/inclusion_fst/image, the unchanged baseIso/sectionsIso/reduce definitions, and the concrete failure targets. appLE_of_eq transports equal scheme maps with both dependent open-inclusion witnesses by substitution and proof irrelevance. inclusion_fst and reduction_map have the required contravariant composition directions. preimage_top only normalizes the entire open; it does not restrict sections or remove opens. The original coefficient, reduction, and epsilon squares and epsilon_naturality application are retained, with arbitrary original R, X, p and V. Downstream open dual-coordinate/logarithm and norm/trace consumers keep the same section maps and epsilon.

3. **Cartesian chart coefficients.** Read ActualOpenFractionField318.genericEquiv/sourceAlgebra/genericAlgEquiv and OriginalProjectiveFunctionCoordinate318.affineCoordinate/coordinate/kappa/coefficient. Both source constructions use precisely AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec on the same affine polynomial chart function field. The added proof-local instance restores that exact action for genericAlgEquiv.commutes; it is not a new global algebra or a different generic field. The composed coefficient equation direction, original chart, kappa and every polynomial q are unchanged. The original pullback H and dominant/integral/domain/open-immersion hypotheses remain intact for coefficient_square/tower and the normal-chart consumers.

4. **Nested open path.** Read the full OriginalOpenPullbackSections318 source including nested_sections and nested_path. Substitution transports k and its dependent IsOpenImmersion witness together rather than rewriting only k inside opensFunctor. The same path f >> g = k, full image opens, original pullback associator, sectionPull and ambient presheaf restriction are retained. No subset of the original full-open sections is substituted and no hypothesis is weakened.

## Verdict and limits

No blocking source-level defect or weakened theorem statement, coefficient action, map, index/open coverage, or local hypothesis was found in these bounded changes. They are suitable candidates for hosted Lean replay. The r73 explanatory word 'postcomposition' was corrected to 'composition on the left'; reviewed Lean bytes remained unchanged.

Elaboration, definitional equality reduction, kernel success, recursive axiom audit and all later consumer modules remain unverified until hosted CI checks the exact successor commit. A failure later in an unchanged consumer is not excluded. This report does not authorize refreshing an accepted application binding or changing any historical verdict.
