# Independent source review: scalar inverse-row factorization

Reviewer /root/lean_review_resume; author /root/arithmetic_repair_resume. Internal model source/application review only. No Lean/Lake executed locally; no kernel pass or independent mathematical acceptance. Baseline a2d615a4183174328321ea21d60879add229de3a; run43534276453; observed weighted predecessor forward-original-weighted-weyl-r22-replay-r5, artifact14089268437.

## Exact evidence

ScalarForwardWitness318 before9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c; candidateca11da39e55cc2a5b17d141662937e85b94162682bf7c5fdeecc21a53126a0c4. FORWARD_APPLICATION.md17b85c67dcdca7977856373b30eb5e187190e0aa2eda74e86520d94c04c74ad5. Exact weighted failure loge65ac6febb69377588cd4a434eb619b2dc35e7378bf578fad6601cc019150e9d.

I verified weighted RESULT.packet_sha256 against the published intake. The module failed in4.979 seconds with exactly two unsolved branches, r265 and r276. Earlier r280 and lexical failures are absent from this diagnostic, not a module-wide pass. Before bytes match both published weighted-r5 and descent-r5 copies. This source review has only the weighted current failure evidence; each later successor must bind its own hosted result before claiming an observed frontier.

## Changed applications

I read the full before/after/diff, exact diagnostic, all input/fill definitions and the literal Raw318FinalReplayData rows. The theorem scalar_rows header, nine input/witness definitions, full row list r263 through r281, hypotheses and seventeen other branch proofs are unchanged.

The exact r265 row is -1 plus the five terms with common slot298: coefficient101783690143177584 times each of w0 and w118, coefficient267108917866935984 times w296, coefficient533801448346128768 times w297, and constant4376874610839020. The unchanged fill supplies slot298=1/inputR(w0), slot296=inputX(w0)^2, slot297=inputFourth(w0), and hq gives w118=w0^2. Thus the grouped coefficient is precisely the defined inputR(w0), using inputX(q)=q+q^2. The new hrow equality is exactly the literal row, not a replacement relation.

The r276 row has the identical five-term coefficient group times slot309 plus -w37. fill supplies slot309=w37/inputR(w0), so hrow is exactly -w37+inputR(w0)*(w37/inputR(w0)). No nonzero condition on w37 is needed for this row cancellation, though the original theorem's hH remains for the other rows.

Each hrow is proved by literal row/fill/hq normalization and ring after unfolding the unchanged polynomial definitions. Both sides contain the same inverse expression, so this stage only factors the numerator and does not assume nonvanishing or perform a domain restriction. After rewriting hrow, field_simp[hr] uses the original exact hypothesis inputR(w0)!=0 while inputR remains named. This avoids the previous premature denominator-polynomial expansion that left a differently normalized inverse after clearing denominators. Ring closes the remaining original rational identity. All arithmetic coefficients and rational constants are preserved.

The domain is still every rational assignment and integer n meeting h0,h1,hq,hroot,hr,hH,ha, not an integer-only or sampled subset. All nineteen constraints are retained in their original order on the same fill; Kummer roots/norm maps, pole scalar, quotient and the consumer ScalarCompleteSource318.full_rows remain unchanged. No source of a separate speculative pole/complete-source repair is included. Imports, existing resource options and trust settings are unchanged.

## Conclusion

No source-level blocker found in these two local factorization routes. Suitable for exact-copy successor propagation and hosted checking. Exact tactic elaboration and kernel validation remain pending; the prior source review of row280 does not certify these new branches. Final propagation must verify each packet's own evidence and all source/order/hash/ancillary classifications.
