# Exact compact quotient proof-boundary repair

Replay42654444580 at68796d427394da46dac1eb8bce578778e2c0dd89 tested frozen222r1 intake013f7b500d7d2421fead393ebab9ac32a415f5065380cb2292a89e3962196cd4.222 verified predecessors were reused and nine drafts passed. LocalPointDifference318 passed in2.319s. CompactLocalPointCoding318 failed in2.119s at only lines63 and125. The earlier quotient map_nsmul repair now passes. Exact receipt is preserved in frozen222/hosted-failure-687-replay.

The metric-ball simplification leaves `(t-z).1` and `(t-z).2`. Add the pinned generated Prod.fst_sub and Prod.snd_sub equations, which are the additive versions of the primary Prod.fst_div/snd_div in Mathlib/Algebra/Notation/Prod.lean at the pinned56a0058 revision. Both primary proofs are rfl. This exposes exactly the coordinate differences used by close_points.

The by_contra! route introduced an order comparison through Real.linearOrder.toLT and then asked simpa to identify it with opaque Real.instLT and NormedField.toAbsoluteValue. Replace that tactic route with direct le_of_not_gt. After the negated membership argument, change the literal formal-membership disjunct to `1 < ‖x‖` and supply the same assumed strict inequality directly. This uses the actual toAbsoluteValue definition (toFun := norm) and original point xRep projection. No new mathematical hypothesis, data, statement, subgroup or operation is introduced. The existing scoped transparency option and finite1M budget remain unchanged.

227 Lean sources are exact228r1 copies; CompactLocalPointCoding318 is the only changed source. The six substantive228 count/orientation modules are unchanged. Hosted Lean validation remains pending; no local Lean was run.
