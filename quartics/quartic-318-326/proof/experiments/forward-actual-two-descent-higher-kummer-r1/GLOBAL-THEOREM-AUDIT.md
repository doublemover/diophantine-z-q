# Exact global theorem boundary

The actual source manuscript quartic_v13.tex lines1157-1190 and7878-7888 uses three separate global stages:
1. Selmer dimension3 plus actual Kummer exactness gives rank plus dim Sha[2]=1. The Cassels-Tate pairing on the finite quotient of full Sha2-primary modulo its maximal divisible subgroup, with paired finite primary cyclic factors, gives full Selmer corank1. It does not give Mordell-Weil rank1.
2. The retained restricted converse turns full Selmer corank1 into analytic rank1 on the two positive squarefree parameters congruent11 modulo12.
3. Modularity and the forward Gross-Zagier/Kolyvagin rank-one theorem give actual rational rank1 and finite Sha. This then gives actual Sha[2] vanishing and the original beta points.

The pinned Mathlib tree contains elliptic group, heights, elementary LFunction definitions and general cohomology. It has no supplied Cassels-Tate pairing theorem, actual full Selmer cofinite/corank theorem, or elliptic analytic-rank-one to rational-rank-one theorem. Repository manuscript statements are not Lean proofs of these. The present packet proves actual full2-primary Sha level finiteness/cyclicity, infinite2-divisibility, and the exact finite-quotient alternating algebra needed in stage1, not the missing global pairing producer or stages2/3. The pairing hypothesis in its final conditional theorem is explicitly quantified; no instance or axiom silently supplies it.

No nondegeneracy of the restriction of Cassels-Tate to F[2] is used. That restriction can be degenerate. The finite quotient itself is proved cyclic in this one-dimensional situation, and an alternating pairing on a cyclic group is identically trivial; nondegeneracy would therefore force that quotient zero.

Manuscript SHA256: 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd
Pinned tree SHA256: 316a94628edddbe7f136d910529656fe62eae01c164813fa15bcb11dbbe988c4
