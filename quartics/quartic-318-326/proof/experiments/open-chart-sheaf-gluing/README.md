# Actual open-chart sheaf transition gluing

This8-source draft extends the explicit module matching-family construction
with actual sheaf transition inputs and original local-chart module recovery.
Five predecessor sources are unchanged from open-cover-module-gluing.

OpenSheafTransition318 takes genuine sheaf isomorphisms on original pairwise
opens in their canonical over-open model, with an identity and an actual
triple-overlap cocycle. Evaluation derives all common-subopen linear maps,
restriction naturality and the scalar cocycle required by matching-family
object gluing. Normalization uses the original overFunctorMap at both endpoints.

OpenSheafGluing318 constructs the actual global sheaf and proves that its
recovered chart isomorphisms realize the exact original sheaf transition,
not merely isomorphic local objects or equality of section classes.

OpenChartModuleImages318 takes unchanged sheaves F i on the original chart
schemes, forms their actual direct images, and recovers F i by the original
open-immersion restriction/direct-image counit. Subchart comparisons retain
the original restriction composition and actual inclusion equality. An
original local pair-transition can be converted to an ambient over-open
transition through these exact comparisons. Given coherent ambient transition
data, the glued sheaf recovers each unchanged original F i.

Historical scope: accepted CocycleModule318, CocycleActualLocalFrame318 and
CocycleCanonicalTransitions318 already construct lines from unit cocycles
with exact transitions. The new construction handles arbitrary module sheaves;
it is not evidence that the previous unit-cocycle gluing argument was missing.
Those accepted line/frame arguments can be reused in the eventual line join.

Remaining joins are explicit: prove the converted local pair transitions
inherit the original scheme triple normalizations, refine arbitrary local
line frames, establish changing-base-chart compatibility of affine fppf
reconstruction, and apply the gluing theorem to that exact datum. No complete
non-affine fppf stack theorem, represented Jacobian or arithmetic theorem is
claimed from this packet alone.

Static bindings/imports/placeholder checks and audit-history self-tests are
required. No local Lean ran. Complete8-source hosted strict replay, recursive
axiom audit and independent acceptance remain pending.
