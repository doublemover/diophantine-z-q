# Independent Bicanonical transport source review

Verdict: PASS for the exact source-level repair below. This is not Lean acceptance, a whole-packet result, or a propagation/current-packet contract review. No local Lean was run.

Reviewed candidate `IntegralOriginalBicanonicalRestrictions318.lean`: `f44a92128cd78998edbb10ee86acce8df7359380de8924ebd8c74cbdea25247f`; published predecessor `adefcb08f9717a19cb7b5d926415a74f5614c440a8542a8b47a4f034841452d6`.

## Authentic observation and exact delta

Run 43611323966 at 2428de0d42f12dc71e2bc6f19495025a5912d41c, center-r69 artifact 14120832731, official digest f534a7968dabb1c1b329a12456033d8856141ee34f5861d64beb5ef04a242633. I independently matched the ZIP digest/CRC/all extracted members, exact own RESULT, published intake, and log. All preceding recorded commands pass; this module fails in 10.287 seconds. Its two errors are the rewrite-matching failures at 93:6 and 112:6, with h/a/omega metavariables and the expanded tensor carrier in the attempted pattern. This does not establish a unique conversion cause.

The sole delta replaces those two `unfold`/under-inferred rewrite blocks by local, fully specialized `transport` equalities and `rw [transport]`. Restoring those two old blocks reproduces the entire predecessor byte-for-byte. Existing theorem statements, declarations (including the preceding two abstract helpers), import list, options, maps, original proof tails, and caller premises are unchanged. No new global declaration or assumption is added.

## Native applicability and full-domain preservation

The actual `IntrinsicTensorChartSections318.weightedSquare_restrict_to` takes j, p, h, f, jT, hC, route, himage, a, omega in exactly the supplied order. Its result transports BOTH the coefficient by f and the genuine universal differential by `AlgHomDifferential318.map f`; the square remains inside the actual intrinsic tensor sheaf. No coefficient-only or point-value substitute is introduced.

For every i:Fin 4 and n:Fin 2 the branch specialization uses R=Q, S=IntegralBranchCoordinates318.B Q c i, T=ContactIntrinsicFrames318.BranchRing c i, the existing branchEquiv, exact original branch embedding/structure equality, branch_route/branchLE, original integral branchCoefficient, and D of the original sourceCoordinate. I checked the published branchEquiv target and actual BranchRing alias. For every n:Fin 2 the infinity specialization uses the original rationalOrderEquiv, the exact infinity embedding and structure equality, infinity_route/infinityLE, original infinityCoefficient and D of the reciprocal coordinate. InfinityGlobalChart.InfinityOrder is the original InfinityOpenChart.OpenOrder, matching the native equivalence target.

The explicitly typed left sides use precisely `(tensor c)`, `branchQ c i n` / `infinityQ c n`, and their original restriction maps. On the right the original coefficient/differential theorems and `weightedSquare_integer` are consumed unchanged. J-squared scaling, the two original global q sections, the infinity inverse powers, all four complete branch charts including ramification, and the complete infinity chart remain intact. Existing whole-open equality, not a restriction to a smaller locus, is the goal.

The direct unchanged consumer `IntegralOriginalGlobalPair318.local_eq_restriction` uses both results over Option(Fin 4); its compatibility and original_identity continue to refer to the same global sheaf and full cover. These are downstream source consumers, not new hosted passes.

## Evidence and limits

The companion checker binds the exact candidate/before/diff/log/RESULT/repair metadata, official artifact metadata, published APP/intake, eight owner-supplied project primaries, and five additional exact Git primaries independently read for the equivalence/carrier checks. Concrete elaboration of the typed transport equalities and remaining conversion/rewrite tails is still hosted-unverified. The Common production source and diagnostic lane are outside this source verdict. A future successor's complete closure, current nine obligations, provenance and final metadata still require separate propagation review.
