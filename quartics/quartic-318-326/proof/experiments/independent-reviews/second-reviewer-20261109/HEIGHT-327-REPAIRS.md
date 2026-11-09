# Bounded review of the 3272849 height repairs

Reviewer: /root/advance_height_realization. Implementer: /root/complete_analytic_geometry. Date: 2026-11-09.

This independently reviews only the three narrow successor diffs authored by the implementer. The reviewer authored older height constructions, whose separate independent review remains main-integrator-owned. No local Lean execution was performed; hosted elaboration is pending.

I read the exact failed RESULT/logs under build/ci-review-3272849 for the three predecessors and compared each successor source. Each packet changes precisely one Lean source; all remaining source files are byte-identical. No theorem statement's mathematical content, hypothesis, coordinate, scalar action, or consumed object is weakened.

## Actual prime-local tensor map

height-good-local-integrality-r7, intake 227581c0c283ce6f19f468947ed0e2eba677d01ae1bae7d8b3ed6ff1126e7b33, changes IntegralContactLocalSections318 only. The predecessor passed thirteen sources before failing to infer the target ring of IntegralCotangentTensor318.map from the actual atPrimeFrame. The repair explicitly specifies R, B=Localization.AtPrime P, and K at both tensor maps; the localized theorem application also specifies A=Order R c. These are exactly the rings and scalar tower already displayed in the theorem hypotheses. The actual reduced quotient producer, prime localization, nonzero/nonunit base parameter, DVR and fraction-field hypotheses are preserved. This is type inference guidance, not replacement of the frame by an assumption.

## Original branch generic tensor

height-integral-branch-tensors-r8, intake 02e6483b1e6f6b5b9b0d34b76805ce92ebd80130e830df63858e07ed8bc7bbfc, changes IntegralBranchGenericTensor318 only. Opening Polynomial resolves the displayed unknown X in the existing free/flat argument. In mapped_quartic, typed hC identifies the image of each polynomial constant with the original R scalar map, and hX identifies X with the same original sourceT through the SourceOrder tower. The subsequent finite product and map numeral simplifications compare the literal four-contact quartic with VerticalSection318.denominator without unfolding the tensor-ring representation of sourceT. This addresses precisely the retained C32/C76832/C343 and mismatched expanded coordinate in the old log. The exact twists, original fraction field, nonzero quartic proof, J squared, and both generic tensor image statements remain unchanged.

## Rational scalar compatibility parser

height-global-open-sections-r10, intake 422507df8d979941ce173db217ded36b5d717732237b034e488e4e0c38b35f20, changes IntegralRationalOpenComparison318 only. The sole change moves commutes' onto its own structure-field line. The same typed RingHom.map_rat_algebraMap proof and comparison ring equivalence remain. This is a parser repair, not a new comparison or altered rational action.

## Checks and limits

Static import/source/hash checks pass for 17/27, 10/103, and 4/198 packet/baseline modules respectively. Exact changed-source lists were independently checked. Audit-history self-test passes its structural negative controls. The new height-integral-global-pair-r1 closure does not import any of these three final consumer modules; its frozen source binding therefore need not change for these repairs. None of these checks is claimed as hosted Lean success or a full arithmetic theorem proof. Bounded source review supports scheduling the three frozen successor candidates.
