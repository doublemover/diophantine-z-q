# original-finite-quotient-reconstruction-r68

Draft successor to `original-finite-quotient-reconstruction-r67` at `977040de03da47698b89a3345d93e2ffcbc2220c`.

## Exact hosted evidence

Run 43578868567, job 132399604823, artifact 14107409816. OriginalFiniteDeckDegree318 passed in 1.066 seconds. OriginalQuotientRankFixed318 failed in 2.268 seconds. Its first error rejects the local baseIntegral instance because the target hides p and Y; subsequent errors cannot synthesize base integrality or irreducibility. The original local actualBase likewise depends on the hidden morphism.

## Bounded repair

Replace hidden-morphism local instance declarations by explicit baseIntegral p and the exposed actualBase p definition whose body is exactly the original quotient-generic map composed with the original rational coordinate. Install these constructed structures with explicit letI scopes in rank_eq_coordinate_degree and fixed. This intentionally changes the public type-scope text, but adds no caller premise, changes no coefficient action or map, and preserves all original explicit arguments and proof calculations.

## Scope and verification

80 root modules in the original order; 1 changed and 79 unchanged. No modules added or deleted. Original imports, resource limits and trust options are unchanged. No local Lean, Lake, declaration audit or compiler was run. Source review, structural checks, hosted kernel checking, whole-packet success and independent mathematical acceptance are separate.

Hosted elaboration and kernel checking of the scoped original rank and fixedness application remain pending. The direct OriginalFiberPointReconstruction consumer still contains its own hidden-p local instances and is not modified or claimed verified. Source review and Python admission are not module, packet or theorem acceptance.

The current application contract is newly authored for this exact change, not inherited approval. Hosted evidence is the actual predecessor result, never a successor pass.
