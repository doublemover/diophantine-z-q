# Independent preventive API source review, run 43519890754

Reviewer: lean_review_resume. These two modules have NOT produced observed hosted failures in this run. This is fresh independent review of authorized preventive changes, not a claim that either module passed Lean. No Lean/Lake invocation, source modification or push was performed.

## Bound source snapshot
- FourRootCoordinateRingSigns318.lean: before `937983452a639845a5bc8a16185f8ff63bd57812cbdb9dc5e0c0ac7c2b6685b3`, after `d0f7d9b6cb7bf684aea17f89b7f3e5e48ce93fd4c5fe1b30caa8eb6b8fd9e269`.
- FourRootInfinityCoordinateRing318.lean: before `b0d15b401900e87ed0da3179153e0ecc74b2496d6a36845ccf4c3a6758734d78`, after `792877ee0474f4d831884346f6faa25b432431146b61cc861ba19a78db56adfc`.
- APPLICATION.md: `ad131156d432a12dc12313444038c80603a7b3f0dcb5c603e70cf83e722c28bd`.

## Source findings
No source-level blocker found.

FourRootInfinityCoordinateRing318 retains Option (Fin 4) polynomial variables with none denoting u and some k denoting every normalized root s k. Pinned Lean Option.elim takes the option first; the new explicit lambda computes u on none and s k on some k. This corrects the aeval input consistently in the quotient lift, kernel proof and coordinate theorem. It does not change the intended evaluation map. The lifted algebra still quantifies over every commutative complex algebra S, every u, every s, mandatory h0 : s 0 = 1, and every hs equation.

The equation/ideal/coordinate definitions and all relations are unchanged. In particular equation none is X(some 0)-1, while equation (some k) is X(some k)^2-1-C(b0-bk)*X(none)^2 for all four k. The proof still checks all ideal generators, using h0 for normalization and hs for every quadratic relation. The model therefore retains the normalized eight infinity signs, not a sixteen-sign unnormalized replacement. I read the actual InfinityPoints/InfinitySigns definitions and normalized sign-action consumer.

lift_coordinate's explicit change computes the same quotient lift on its defining class. The pinned Ideal.Quotient lift_mk and liftₐ_apply are definitional rfl identities; MvPolynomial.aeval_X supplies the unchanged evaluation of that variable. The formula itself uses the corrected option-first syntax without removing k or any hypothesis. This mirrors an observed affine analogue but remains an unobserved preventive fix here. Its success still depends on hosted elaboration and kernel validation.

Algebra.algebraMap_self_apply is the actual namespace of the pinned self-algebra-map identity. The one Infinity point proof and three CoordinateRingSigns references are fully qualified only. The latter file is byte-equivalent to its before source after undoing those three qualifications. Its finite/infinity endomorphisms, involutions, algebra equivalences, all points, and signed formulas are unchanged: u maps by epsilon0 and s_i by epsilon_i times epsilon0. No scalar representation, branch constant, normalization, coefficient field, coverage, hypothesis or public intended theorem changes.

No import, resource/trust option, admitted axiom or baseline/cache change was introduced. The malformed old Option syntax did not elaborate, so this report asserts preservation of the explicitly documented mathematical evaluation, not a prior elaborated term identity.

## Evidence housekeeping and boundary
At inspection there were duplicate .patch and .lean.patch files, with the shorter Infinity .patch retaining the earlier simp-only proof. The owner was notified to canonicalize or clearly label obsolete patch evidence before packet inclusion. This report binds the final source hashes above; it does not approve an ambiguous stale patch. STATUS and SOURCE_VALIDATION already bind those final source hashes correctly. A later propagation check must verify only final canonical source/evidence is copied.

No complete packet, point equivalence, action or theorem is called Lean-passed or independently mathematically accepted by this source-only review. Hosted compilation, all remaining consumers and axiom auditing remain required.

## Pinned primary hashes
- Mathlib_Algebra_Algebra_Defs.lean: `8cd3931aa8f1e5295c6b7892a70dcf8f7e231df28ff0b6bed1a20b14a5f5a64c`.
- Mathlib_Algebra_MvPolynomial_Eval.lean: `fb0dd2f7f249f9234abcf7cba2deca0cbdcc6cbf05e07adc18714579ba3a3e72`.
- Mathlib_RingTheory_Ideal_Quotient_Defs.lean: `194ac19a4c3c98e7177c683bb89dd8ac09a0f597833f3223b6ee8e944b99bcfa`.
- Mathlib_RingTheory_Ideal_Quotient_Operations.lean: `90cbc7f60b4b6d777c89e9bb09699c5b269b0576a7c95716a11e07cc81614dab`.
- src_Init_Data_Option_Basic.lean: `cf4b95fea5eceebccfd6ce65c172b8b3cd35e8a805b1f2018e59f951a2b30bf9`.
