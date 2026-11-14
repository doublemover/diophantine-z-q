# Independent source review: ScalarForwardWitness318, run 43519890754

Reviewer: lean_review_resume. Scope: exact candidate source, unchanged producer data and consumer contract; no Lean/Lake invocation, push or source modification.

## Bindings

- Before: `115729a9f8748290186bb0396ed78dd0355ec3fd93ff8a7ffb02f653dad675a5`.
- After: `9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c`.
- FORWARD_APPLICATION.md: `e64bef67fb9832a7522c46fadc4271898f7e8b3fa7d0abc68fb3749d6abb4ccc`.
- Raw318FinalReplayData.lean: `c563f76c563192a218c3bdf22714ab73f36d3a0ed9c629a346d7d3bb9fa80457`.
- Exact descent hosted failure log: `8e1e390e3af7425e21c9e1552e240655372afef54aff4c6c7bf9fd9240b56101` (artifact 14083506993, head 58753ec5f3b41268c5ceedae5264593b4f2aa0de).

## Findings

No source-level blocker found. The hosted diagnostics actually show malformed comparison parsing (unknown nputX/nputFourth), failed no-progress cleanup steps, and the r280 unsolved goal. Whitespace restores the intended rational inequalities, not a different condition. Wrapping only normalization steps in try does not close or discard any proof obligation; the existing following field_simp/ring or change/rw proofs remain mandatory.

I checked the complete candidate and literal r263 through r281 definitions. All nine witness definitions (inputX, inputFourth, inputR, N, Q, W, quotient, poleInput, fill) are byte-identical; scalar_rows' full declaration through its conclusion is byte-identical, including S, w, n, h0/h1, hq, original labelled hroot, hr/hH/ha and the ordered 19-row list. The Kummer real/imaginary branches r272/r273 and the two squareclass statements/proofs are unchanged. No new axiom, admitted proof, hypothesis, coverage restriction, evaluator or resource option was introduced. Existing maxHeartbeats/maxRecDepth settings are inherited unchanged, not newly validated.

For r280, fill maps 312 to Q squared, 313 to the existing quotient, 311 to N minus one, 296 to inputX squared and 297 to inputFourth, while 118 reduces using hq. The four quotient coefficients are precisely 114444 times the three inputR coefficients and one plus 114444 times its constant. I independently recomputed those four integer identities. The remaining Q-squared terms are exactly minus inputR times Q squared. Thus the proposed local hrow is a polynomial identity in the unchanged N, Q and quotient values, not a replacement row or surrogate witness. The local hquot uses exactly the pre-existing nonzero denominator ha. After rewriting hquot and unfolding W, the target is minus N squared minus inputR times Q squared plus W, an identity. Keeping N/Q/quotient closed in hrow avoids the previous unnecessary expansion of the high reciprocal power without changing their meaning.

The immediate ScalarCompleteSource318 consumer still applies scalar_rows to the same arguments and carries the same completed assignment and full literal row set. Its separate arithmetic Certificate and Anchor assumptions are neither added nor removed here. The speculative ScalarCompleteSource318 normalization patch is not part of this review or candidate.

## Validation boundary

This is independent source/contract review, not Lean acceptance. Optional numerical sampling is neither used as a proof nor needed for this conclusion. Hosted Lean must still validate all newly reachable normalization branches, elaboration and kernel/resource behavior; earlier failure prevented that assurance. No complete packet or final arithmetic theorem is claimed passed.
