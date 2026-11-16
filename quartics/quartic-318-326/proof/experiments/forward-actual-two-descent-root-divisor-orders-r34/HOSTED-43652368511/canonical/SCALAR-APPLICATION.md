# Scalar local squares: exact hosted-feedback repair

Base 2e4471d08710d58a1fdc2353b62a30023d88e94e; run 43652368511. The small-prime predecessor now passed, but ScalarLocalSquares318 failed. This is an isolated uncompiled candidate, not active or accepted.

1. Required inputs: same arbitrary prime p with Fact p.Prime, p-adic integers u,v and literal near-square strict norm inequality. Same unrestricted integer k in the three specializations.
2. Objects: polynomial X^2-C v, Hensel root, integral and rational square witnesses remain identical. No witness or local-squareness assumption is inserted.
3. Coverage: all k and all circuit assignments in the original theorems remain; primes 2,3,17 and congruence shapes 1+8k,1+3k,8+17k are unchanged.
4. Maps: existing integral-to-rational p-adic maps and the actual normalized multiplier/pole constructions are unchanged.
5. Scalars: derivative remains exactly 2u, norm threshold its square. Norm of each prime is exactly its real reciprocal; 2*5=10 is explicitly normalized for p=17. Ramified p=2 requires valuation 3, not an odd-prime surrogate.
6. Identity with consumed object: the polynomial evaluation/derivative equalities are proved before entering the norm comparison. Norm facts specialize the pinned PadicInt.norm_p to the same p-adic integer ring, avoiding theorem-index/numeral syntactic mismatch. No replacement norm is used.
7. Exceptions: all original assumptions and scopes retained. Arithmetic residuals remain exact; no nonzero, coprimality or field hypothesis added to original statements.
8. Propagation: one canonical isolated source. Future descent and weighted successors must receive byte-identical source wherever present, preserve their own before/results evidence and native contracts. No current packet or historical snapshot edited.
9. Verification: genuine errors at derivative normalization and three prime-norm rewrites drive these proof-only edits. Original imports/options/statements unchanged. Primary source is Mathlib PadicIntegers.lean at 56a005855ea17e0b0958f73ec801ae140b0a1679, lines220-325. No local Lean/Lake; independent review and hosted elaboration/axiom audit remain required.
