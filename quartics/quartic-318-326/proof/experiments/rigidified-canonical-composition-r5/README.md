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

## Revision r3

Hosted run42576170502 at1ec2917 compiled the first38 modules. The next source
omitted section hypotheses used only inside composite_pointed, and its broad
componentwise simplification hit the bounded heartbeat limit. This revision
explicitly includes both original hypotheses, restoring the intended parameter
list at the existing consumers, and uses finite natural-transformation-level
comparison/projection simplifications. Forty sources remain byte-identical.
The actual maps and equations are unchanged; the original600000 heartbeat
bound remains. Exact failure evidence is retained. Full hosted replay and
recursive audit remain pending; no local Lean ran.

## Revision r4

Run42578244224 at aa07a2c confirms the two preceding declaration repairs,
then leaves natural-isomorphism app projections unreduced in the final
restriction composition calculation. This revision adds only Iso.app_hom
and Iso.app_inv to the finite simplification, using the exact API already
consumed in accepted PullbackChartComposition318. Forty source files remain
byte-identical. Actual maps, statements and hypotheses are unchanged. The
exact failure is retained; hosted41 replay and recursive audit are pending.
No local Lean ran.

## Revision r5

Run42579994089 at cee0c58 passes39 predecessors including the complete repaired PointedPullbackComposition. The next named naturality calculation leaves only a composed-functor map unreduced. This revision adds Functor.comp_map normalization there. Forty sources remain byte-identical, all actual maps and hypotheses remain unchanged. Exact failure evidence is retained. Full41 hosted replay and audit pending; no local Lean ran.
