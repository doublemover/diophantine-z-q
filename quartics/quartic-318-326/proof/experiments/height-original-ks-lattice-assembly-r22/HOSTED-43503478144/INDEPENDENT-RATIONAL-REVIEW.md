# Independent rational-infinity source review

Reviewer: lean_review_resume. Scope: candidate against hosted run 43503478144 at head 56773da3e1a8045d885059ae17053fcbf0af6067. No local Lean/Lake execution or push. This report is source review, not Lean acceptance.

## Bound inputs
- IntegralRationalInfinityMap318.lean.before SHA256 b3a37fb56e341a83585bf2a8c887c2b006aecde39b5d9e8ed1307dd99469064d
- Candidate IntegralRationalInfinityMap318.lean SHA256 f72d6593711066005480226d7c8cda9c3283acce8a3d9e9b67211fb7d4e0bace
- Exact hosted log SHA256 479769d87d2263dfc82621b74894cb8f9b56f0081db66755086f089972b27fc3

## Findings
1. Hosted line 76 mismatch retains commonMap.toRingHom application, so root_zero did not rewrite. The candidate explicitly changes that application to the identical AlgHom application, then rewrites the proven signed root_zero. The unit inverse and sign are unchanged. The change mirrors reciprocal_coordinate in the already-existing dependency.
2. Hosted lines 101 and 106 exceeded recursion depth during concrete endpoint matching. The private rational_order_ext premise now uses the literal two-stage polynomial/localization/order coordinate, exactly IntegralInfinityChart318.coordinate. ThreeRootCoordinates318.ringHom_ext still checks equality on the entire coefficient ring; localized_polynomial_ext still establishes that equality from rational constants and X. All three ordered root equations remain universally quantified over Fin 3. No public theorem is weakened.
3. hroot unfolds only the actual originalEmbedding composite, exposes its rationalOrderEquiv application, and rewrites its generator equation and InfinityOrderCoordinates318.generator_embedding. This is the same normalization pattern as original_coordinate in IntegralInfinityOriginalField318, not a replacement embedding. The final transitivity still identifies the original ordered ratio in the same original field.
4. No public statement, assumption, carrier, morphism, solver budget, index coverage, or consumer claim changes. No new axiom/sorry/abstract comparison premise.

Conclusion: no source-level blocker identified for this exact candidate. The smaller matching obligations plausibly address the observed recursion failures, but only hosted replay can establish elaboration and strict proof success. Propagation into successors is a separate byte-identity check.
