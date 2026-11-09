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

## Validation

The 41-source closure has three new sources and 37 byte-identical producer
copies and one further repaired producer from the overlap r2 packet. Eight producer modules are recent
drafts, not accepted-baseline results. Source/hash/import/placeholder validation
passes. Hosted checking of r2 confirmed the earlier composition repair and
then left a reflexive `map`/`mapIso.hom` equality in the pointed-pullback proof.
This packet closes that equality explicitly without changing its maps or
statements; see `SOURCE_REPAIRS.json`. Local Lean compilation was not run, as instructed. Hosted strict
compilation, recursive axiom auditing and independent acceptance are pending.
No previous compiler receipt or review is treated as acceptance of these new
applications. No unconditional arithmetic theorem is claimed.
