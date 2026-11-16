# Exact scaled-theta residual repair

Own torsion28 at a257620302c4a784c6c1f1dc9838c8fd61954de3, run43658730606. Unscaled holomorphy passed2.771s; scaled holomorphy failed2.621s. The candidate is isolated and uncompiled.

1. Required inputs: same original τ with 0<τ.im, positive real scale a, fixed frequency predicate P with DecidablePred, and every z in the full complex vector space. No new assumptions or dropped positivity binders.
2. Constructed objects: actual scaled theta term, original derivative, derivativeBound and every fixed characteristic subseries unchanged. Only three proof surfaces are repaired.
3. Coverage: full C² Frechet differentiation, every integer frequency n and every fixed subset P; P is selected independently of evaluation point. No finite-sum or one-variable substitute.
4. Transition maps: the norm proof exposes the existing slope at its exact expression. In each P n branch a pointwise proved function equality identifies selectedTerm with the same term or constant zero, then rewrites the function under HasFDerivAt.
5. Scalar factors: slope remains abs(n1)+abs(n2), derivative remains term*(2*pi*I) times the same linearMap, scale a remains in the quadratic exponential constant and all bounds. No factor or sign changes.
6. Consumer identity: the zero branch uses pinned hasFDerivAt_const(c)(x) with c=0:Complex and x=w:ComplexVectors, explicit base field Complex. This is the actual rejected target, not a derivative of a different function or at a different point.
7. Exceptions: both frequency branches, including zero frequency, all points in the original local unit ball, every positive a and original hτ remain. No cancellation or nonzero input vector premise.
8. Downstream effects: unchanged imports, options, theorem types, original convergence, and all later consumers. Matching current source copies may be propagated only with their own evidence; any unreached copy is explicitly preventive. The unscaled source is not modified.
9. Verification: exact own RESULT/intake/log and pinned Mathlib FDeriv/Const at56a005855ea17e0b0958f73ec801ae140b0a1679 are bound. Source review and future hosted closure/audit acceptance remain separate. No local Lean/Lake, resource/trust change or full lane claim.
