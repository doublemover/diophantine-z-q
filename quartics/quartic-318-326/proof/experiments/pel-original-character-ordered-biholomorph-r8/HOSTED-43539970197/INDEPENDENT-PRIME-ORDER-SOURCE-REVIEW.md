# Independent source review: actual prime-order conjugation

Run 43539970197, head 7a5f079f2a82fa6f21db0e060d9bca1af9956a0b. Candidate PELPrimeOrderConjugation318.lean: before 92dfdf3c5a5b41508d1d13b03dde86247ea8053b83de565fdd67400fe58e1a8a; after 94e92e91e28b067df81f66536dd1f38cdf6a4d6c36a6e91a3a7d1f64bd216402.

Disposition: no source-level blocker found. No Lean/Lake was run; actual successor compilation and declaration audit remain pending. This is not independent mathematical acceptance or a whole-packet success claim.

Read the complete before/after module, exact character-r7 hosted diagnostic, application comparison and the native PELOrderReductionThree318.coordinates_mul theorem. Only orderEquiv.map_mul proof tactics change. The exact residual is coordinatesEquiv(forward i (coordinatesEquiv.symm(coordinatesEquiv a * coordinatesEquiv b))) = coordinatesEquiv(forward i a) * coordinatesEquiv(forward i b). The old simplifier reintroduced coordinatesEquiv a * coordinatesEquiv b before inverse cancellation, leaving forward_product unused.

The new proof explicitly rewrites that original product backward using coordinates_mul a b, yielding coordinatesEquiv(product a b) inside the inverse. It then simplifies only AddEquiv.symm_apply_apply, so the inverse cancels without re-expanding the custom coordinate product. Finally forward_product i a b and coordinates_mul (forward i a) (forward i b) produce exactly the required native order multiplication. The last equality is the actual product theorem Subtype.ext(embed_mul a b), not a false assertion that the additive coordinatesEquiv preserves pointwise function multiplication.

Both surjectivity decompositions still cover every original order x,y. All four literal forward/backward integer matrices, their inverse/additive/product identities, the rational normalizer elements, actual_forward/backward inner-conjugation identities, ring-equivalence maps and actual orderEquiv_value/normalizes_order consumers are byte-identical. No smaller generator domain, norm-one restriction, scalar change, new hypothesis, declaration signature, import, resource option or trust change is introduced. The distinction between rational order normalizer and polarized-surface isomorphism is retained.

Provenance independently checked: before bytes equal own published character-r7 source; manifest before/after/log hashes recomputed; own RESULT carries intake a250978cc33fac0cd5ff6e20f208308fc7a6d5dc88d5011b98d5b7cdcc7bb1af. Artifact 14092146573 log SHA21d824a760bb5f2ca4067e6e19d7414ebe683c110e88af63a7307ea20fe7050a reports this module failed47.522 seconds, with only map_mul unsolved plus linter warnings. Its preceding PELLevelThreeSimilitudes318 passed2.119 seconds; this does not certify the whole packet. Sibling trace propagation still requires its own evidence/predecessor-byte comparison.

PRIME-ORDER-APPLICATION.md SHA256: 563803385a82d4398616519a4c4f73c6bcd73e23d0d8e6fb475bc84c86b80c76
PRIME-ORDER-MANIFEST.json SHA256: c0d88ea9aa979d45a7cba54f4b25255f0467d88b45724ff71fc3f3aa9debb200
