# Scalar inverse-row factorization repair (source-only)

Basis: hosted Lean run 43534276453 at a2d615a4183174328321ea21d60879add229de3a. Weighted packet forward-original-weighted-weyl-r22-replay-r5, artifact 14089268437, stops at ScalarForwardWitness318 after 4.979 s. Its only two reported errors are unsolved goals at lines 91 and 152, the r265 and r276 branches. The prior row280 and lexical repairs no longer report errors; this is not a whole-module pass. A separate own descent artifact must be bound before propagation to the descent successor.

Before SHA-256 9b21f269bbf73da643a7259f71dc67ea835a52aaa97bbb6d449549004bf7038c. Candidate SHA-256 ca11da39e55cc2a5b17d141662937e85b94162682bf7c5fdeecc21a53126a0c4. Exact before/diff/after and own hosted log retained. Raw318FinalReplayData.lean primary source copied without change from the predecessor's earlier pinned evidence.

## Exact required and constructed inputs

The theorem scalar_rows still requires arbitrary S:ℚ, w:Assignment and n:ℤ, n≠0, n≠1, hq:w118=(w0)^2, the same fixedRoot equality, hr:inputR(w0)≠0, hH:w37≠0, and ha:1+114444*inputR(w0)≠0. It returns Constraints on the same list of nineteen literal rows r263 through r281 and the same fill w n. All definitions, declarations, hypotheses, row order, exception conditions, imported sources and existing resource options remain byte-identical. Seventeen branches including the Kummer rows and prior r280 factorization remain unchanged.

Both failed branches expanded inputR before cancellation. The hosted normal form retains inverse factors of a denominator-cleared degree-eight polynomial, whereas hr names the original rational polynomial. The repair separates exact polynomial factorization from division cancellation, leaving the denominator inputR opaque during field_simp.

For r265, fill places 1/inputR(w0) into slot298. Slot296 is (inputX(w0))^2, slot297 is inputFourth(w0), and hq identifies slot118. The literal row equals -1 + inputR(w0)*(1/inputR(w0)). The five inputR coefficients, including the split w0/w118 term, remain 101783690143177584, 267108917866935984, 533801448346128768, and constant 4376874610839020. The local hrow equality is proved by unfolding the exact input-polynomial definitions and ring normalization on both sides, not by assuming denominator nonvanishing.

For r276, fill places w37/inputR(w0) into slot309. The identical five-term coefficient group is inputR(w0), with the independent summand -w37. Thus the literal row equals -w37 + inputR(w0)*(w37/inputR(w0)). The same hq and same original input definitions prove hrow. In both branches, rw[hrow] followed by field_simp[hr] and ring uses only the originally required nonzero hr to prove the exact literal row vanishes.

## Domain, maps, consumers

All nineteen row indices are preserved and every assignment satisfying the original hypotheses is covered. No smaller set of rational points, new witness, extra nonzero hypothesis, changed root, deleted row or special example substitutes for the quantified theorem. Coefficients stay in ℚ with exact arithmetic. Norm and Kummer maps, pole scalar and quotient, and all fill slots are unchanged. The object consumed downstream is still Constraints [r263 S,...,r281 S] (fill w n); the exact ScalarCompleteSource318.full_rows consumer is unchanged. No speculative ScalarPoleRealDomain318 or ScalarCompleteSource318 edit is included.

Source-only independent review is required for these exact two new local hrow routes. Earlier review of r280 does not accept this change. No local Lean, Lake, kernel, recursive axiom or full arithmetic theorem check was performed; bounded elaboration and resulting source acceptance remain for hosted replay.
