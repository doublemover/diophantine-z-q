# Independent source review: original whole-open restriction squares

Reviewer: independent Lean reviewer, run 43539970197 at published head 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b. This is source/provenance review only. No Lean/Lake/compiler was run, no resource limit was changed, and no independent mathematical acceptance or new kernel success is asserted. No source blocker found; final elaboration and performance remain for hosted CI.

## Bound target

- ContactOriginalWholeRestriction318 before: 619d6667786ed04c54d15216d55c7e013e7f3e8250291343a3db5561d80984d8
- Candidate: 7703c3170db29686170082260f439fcea1f3dbed7724381399380a643bd888cd
- POSITIVE_APPLICATION.md: 7ae55130a1e2d55fd6084faf98bba0307a24ba98ddf7e7eb5c94ba5cb7064c7b
- Exact own log: 25d11550cfc2a53eccedc587f7772505e0a84315d385a25c463cc1d8f4ddb015
- Own RESULT: b1cbd79de507d96eb88923915f620e51eabfac3c491f26f5d0b579197a28692e
- Published predecessor contact-original-positive-generators-r67 intake: 5f54b3a831be9da1b9a6522af24cee2d8ce2395d6418dc24b2e2b40a2865e049

Before bytes and RESULT packet identity were independently matched to the published predecessor. The exact hosted log reports only the two concrete square rewrite failures, at lines 83 and 93. OriginalTensorChartWholeRestriction318 passed in that replay; the failed WholeRestriction module has not passed. The rewritten proof retains a potentially nontrivial final definitional-trans endpoint, correctly disclosed in the contract.

## Proof and application

Only finite_square and infinity_square proof bodies change. Definitions, public statement text, imports, existing explicit finite_direct/infinity_direct specializations, image_restriction helper, and options are untouched. The native ContactWholeOpenSectionRestriction318 producer statements were inspected independently.

Each proof first lifts the producer's original square equality by congrArg of the SAME fixed mapIso(eqToIso(overlap_image c).symm).op additive equivalence. Its argument is typed as sections of the actual original L.object on the full image of into c. The direction is image-open to full original intersection, exactly as the existing overlapEquiv. This is not an arbitrary replacement equivalence or a smaller open.

Then congrArg (overlapEquiv c L) of the unchanged finite_direct/infinity_direct equality identifies the original tensor-recovered section with its direct section. Transitivity composes this with the lifted native square and the existing image_restriction equality. The latter uses the original full source section, equality overlap_image c, same image inclusion and inf_le_left/inf_le_right. Its target is the original L restriction to finiteOpen c meet infinityOpen c. The old rewrite failure within a partially unfolded AddEquiv.trans is avoided without changing that equivalence.

Every c, every original global line L and every full-open section remain quantified. Original rings, reciprocal scalar action, tensor charts, comparison maps, projections and inclusions are unchanged. No premise, pointwise/generator restriction or new scalar action is introduced. The 107-source closure and 106 other source bytes require separate successor propagation verification; this report binds the canonical changed source only.
