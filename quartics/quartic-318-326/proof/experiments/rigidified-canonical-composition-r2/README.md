# Canonical composition of actual rigidified pullbacks

Three draft modules address the canonical-comparison obligation isolated by
`rigidified-overlap-descent-r2`:

1. `PointedPullbackComposition318` derives composition of the actual pointed
   restriction comparisons from three applications of the accepted
   `PullbackPathComposition318.assoc` theorem and explicit isomorphism
   cancellation. All scheme maps and equality transports are retained.
2. `RigidifiedCanonicalComposition318` combines that equation with naturality
   and the accepted structure-module unit-composition theorem. The **original
   module-pullback composition isomorphism itself** preserves the specified
   rigidifications. No scalar correction, global-function condition or choice
   of a different isomorphism is inserted.
3. `ContactCanonicalPathComparison318` applies the result to the actual
   full fiber-product test maps. It identifies the earlier rigidity-selected
   `pathIso` with the canonical module-sheaf composition/equality isomorphism,
   including its inverse, using the already proved all-test rigidity.

This supplies a draft bridge from the previously explicit normalized overlap
cocycle to the canonical module-pullback comparisons. It does not construct an
effectively descended sheaf, glue a rigidification, instantiate Mathlib's
fppf descent category, or prove representability.

## Validation and revision

This r2 packet preserves all41 source modules and statements from
`rigidified-canonical-composition`. Forty sources are byte-identical; the only
edit removes a redundant `rfl` in `ActualOverlapDiagram318.vertex1_base` after
`rw [Category.assoc, second_base]` has already closed the exact goal.

Hosted run42574563881 at commit2cdec4e passed the first35 modules, including both
earlier repairs, and then reported `No goals to be solved` at that line66.
The original packet remains unchanged. Exact failure log and RESULT are retained
in `hosted-failure-42574563881`; the new repair and inherited prior repair are
recorded separately. Full41 hosted compilation, recursive axiom audit and
independent acceptance remain pending. No local Lean was run. No effective
descent, represented Jacobian or unconditional arithmetic theorem is claimed.
