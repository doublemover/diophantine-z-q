# Bounded scalar forward-witness repair

Observed source: run 43519890754 at 58753ec5f3b41268c5ceedae5264593b4f2aa0de, descent r4 artifact 14083506993. ActualScalarRoot318 passed, then ScalarForwardWitness318 failed. The weighted r4 predecessor file is byte-identical. Exact before/after hashes are in FORWARD_MANIFEST.json, and the untouched log and RESULT.json are in evidence/. No local Lean was run; all proposed fixes remain kernel-unverified.

## Lexical correction

The tokens `10<inputR`, `0≤inputX` and `0≤inputFourth` split at an unintended notation prefix before the i. The hosted diagnostics report OfNat (Type _) and unknown nputR/nputX/nputFourth, despite the actual input definitions being present. Add spaces around those comparisons, including integer_inputR_large. The intended inequalities and all rational polynomial coefficients stay unchanged.

## Optional normalization steps

The scalar_rows proof has generic cleanup steps which are irrelevant to several particular rows after norm_num. The hosted errors explicitly say simp or dsimp made no progress. Make these normalization-only steps optional with try. This does not admit, discharge, weaken, or skip a theorem obligation: the existing change/rw/norm_num/field_simp/ring proof steps still must close every goal. No new assumption, evaluator, axiom or resource cap is introduced.

## Row280 factorization contract

The required row is the literal Raw318FinalReplayData.r280 at the same fill w n. The original w : Assignment, n : ℤ, S : ℚ and hypotheses h0,h1,hq,hroot,hr,hH,ha remain unchanged. All19 rows r263 through r281 stay in the same order. The actual scalar root, common norm, original signed root and original storage slots are untouched.

Define no replacement object. Prove locally that the existing quotient satisfies `(1+114444*inputR (w 0))*quotient w n = W w n`, using exactly the existing ha ≠ 0 denominator hypothesis. The quotient definition is W divided by that same denominator.

Then rewrite the literal r280 polynomial to

    -1 - 2*(N w-1) - (N w-1)^2
      - inputR (w 0)*(Q w n)^2
      + (1+114444*inputR (w 0))*quotient w n.

This identity unfolds only r280/fill and the existing polynomial inputX/inputFourth/inputR definitions and uses the same hq : w118 = (w0)^2. N, Q and quotient stay opaque during this polynomial verification. Exact integer coefficient checks give:
- 114444 * 101783690143177584 = 11648532634745815423296;
- 114444 * 267108917866935984 = 30569012996363621752896;
- 114444 * 533801448346128768 = 61090372954524360724992;
- 1 + 114444 * 4376874610839020 = 500907037962860804881.

These are exactly all quotient coefficients of r280. The negative Q-square coefficients are exactly minus inputR. The two N-1 terms and constant are exactly minus N squared. After the quotient identity, unfold only W = N^2 + inputR*Q^2 and finish by ring. This avoids expanding the degree8 inputR polynomial inside the15th-power denominator of Q, which produced the enormous unsolved hosted expression. It changes only the proof route, not the polynomial row or its witness.

## Domain, maps and consumers

Every n satisfying n ≠ 0 and n ≠ 1 remains covered. Every rational S and original assignment w with the original hypotheses remains covered. The complete19-element row list is unchanged; no row or branch is removed. The coefficient field remains ℚ, and the quadratic-field root is unchanged. No transition, norm or sign map is altered. The consumer still receives Constraints [r263,...,r281] (fill w n), the exact same assignment and literal rows used in ScalarCompleteSource318, not an equivalent surrogate system. pole_squareclass and pole_squareclass_eleven retain their statements and proofs. The earlier full_rows speculative normalization is NOT included in this candidate.

## Validation limits

Source comparison and exact integer coefficient computations are not Lean proof. Remaining formerly blocked branches must be checked by hosted Lean, along with bounded elaboration and recursive axiom auditing. No complete packet or arithmetic theorem is claimed to pass. Distinct internal source review is requested for the changed factorization route and exact source/contract hashes.
