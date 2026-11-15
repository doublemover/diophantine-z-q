# Actual original level-theta decidability and residue-guard repair

Observed own torsion29 run43661685475 at58f3c3ea56040e8776debb9d9b7a6d12db76ac23. Candidate isolated, no active edits/local Lean/Lake.

1. Required inputs: same τ and hτ:0<τ.im wherever already included, same N:ℕ with existing NeZero N, full r:ZMod N×ZMod N and arbitrary integer frequency k. No positivity/nonzero assumption removed or added.
2. Constructed objects: the same accepts predicate residue N k=r, its DecidablePred instance, levelTerm and levelTheta. Instance proof explicitly presents the underlying equality to native DecidableEq; no classical arbitrary label selection or replacement predicate.
3. Coverage: every original label (all N²), all integer frequencies and period indices, all complex vectors. No finite sample or restricted support.
4. Transition maps: same shift N b, residue_shift and scaled_term_period. The term_period proof splits on the actual unshifted residue equality and explicitly reduces both original and shifted if guards by the same fact.
5. Factors: unchanged positive scale1/N, original integer and period vectors, original multiplier raised to N, same original normalized lattice. Both positive and negative guard branches preserve the exact zero convention.
6. Consumer identity: selectedTerm uses exactly accepts N r; levelTheta remains its original infinite sum. theta_integer/theta_period/original_period, summability and holomorphy consume the unchanged maps and the same positivity proofs. No convergence or periodicity statement becomes an assumption.
7. Exceptional cases: nonmatching frequencies produce zero on both sides, matching frequencies use the original scaled-term identity. r and k may be zero; N=0 remains excluded only by existing NeZero. No exceptional periodic branch discarded.
8. Actual evidence: own RESULT/intake/log bind the current failure after52 successful commands. ScaledThetaHolomorphy now passed1.968s and ThetaQuasiperiods1.768s; LevelTheta failed1.818s at missing accepts decidability and two residual guards. The new source fixes those exact surfaces; it does not claim later declarations or lane acceptance.
9. Verification boundary: only the instance body and term_period proof body change. Public statements/imports/resource options and explicit hτ inclusion remain unchanged. Independent source review, all-copy propagation and hosted Lean acceptance remain separate. No local Lean, new trust/resource option or full PEL endpoint claim.
