# Actual theta real-torus Fourier namespace repair

Observed torsion30 failure in run43664736777 at1785ba5569eff8aebbd69b9236dead5e0fcc3c02. Isolated one-identifier proof repair, pinned mathlib56a005855ea17e0b0958f73ec801ae140b0a1679. No local Lean.

1. Inputs: unchanged arbitrary τ:ℂ, existing strict upper-half-plane hτ:0<τ.im where required, full integer pair n and every real two-coordinate x. The termwise identity itself remains independent of hτ as before.
2. Constructed object: same continuous-map torusTerm and full Banach-space theta sum. The existing Fourier evaluation lemma is global _root_.fourier_coe_apply in the pinned native source, not in namespace AddCircle.
3. Domain: entire real unit torus UnitAddTorus(Fin2), all integer frequencies and all real representatives. No frequency truncation, representative restriction or pointwise-only substitution for uniform summation.
4. Maps: unchanged realPoint,torusPoint,mFourier and ContinuousMap evaluation. The native formula evaluates the same circle character on the same real representative; it is not an unrelated character or normalization.
5. Scalars: exact unit period1, positive Fourier exponent2πI*n*x and original coefficient exp(πI*quadratic τ n) remain. With the correct global lemma both factors expose exponentials, so the existing two exp_add rewrites and ring identity combine to the original theta term. No sign,2π,measure or Haar normalization change.
6. Consumer: unchanged real_evaluation uses actual ContinuousMap.evalCLM on the genuine HasSum, then uniqueness against the original theta series. torusPoint_surjective remains unchanged, including all real representatives.
7. Exceptional cases: n=0, zero coordinates and arbitrary τ in the termwise algebra remain included. Nonvanishing of the theta at every point is not asserted. Existing analytic positivity hypotheses and Banach summability inputs are retained exactly.
8. Own evidence: actual torsion30 RESULT packet hash matches its own current intake. LevelTheta now passes2.470s; ThetaRealTorus fails14.199s after53 successes at unknown AddCircle.fourier_coe_apply and the resulting still-unexpanded Fourier factors. Exact native AddCircle/Multivariate source and authentic log are included. No downstream pass is claimed.
9. Boundary: one identifier changes, all definitions, statements, imports, options, instances and other proofs remain byte-identical. Independent source/propagation review and future hosted verification are separate; no new trust/resource setting or Lean acceptance is claimed.
