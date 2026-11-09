# Arbitrary local line frames glue on the original scheme

This10-source draft extends actual open-chart module gluing to arbitrary
original local line sheaves, without assuming the line is trivial on each
original chart. It retains six exact8-source predecessors and narrowly fixes
two proof-only theorem hypothesis omissions found during source review.

LocalLineGlobalFrames318 takes a global module sheaf M, original local lines
L i on the original chart schemes, and actual isos M restricted to U i ≅ L i.
It refines the original cover by the images of every original local frame open.
The cover proof uses both original cover hypotheses. Each frame is transported
through the actual isoImage of the open immersion, preserving original module
restriction composition, equality and unit comparisons. The resulting Line
has exactly the same global module object M.

OpenChartLineEffectivity318 applies this to the explicit glued module sheaf and
original direct-image counit comparisons. The global line recovers each
unchanged original local line object on each original chart. The inherited
sheaf transition recovery remains exact, not merely an existence of local isos.

Repairs are source-reviewed, not attributed to a hosted failure: retain hs in
OpenModuleSheafGluing318.component_compatible and retain D in
OpenChartModuleImages318.effective. Include directives precede any docstring.
All original data and mathematical statements remain otherwise unchanged.

Accepted unit-cocycle line reconstruction and exact transition recovery already
exist in CocycleModule318/CocycleActualLocalFrame318/CocycleCanonicalTransitions318.
The present arbitrary-module gluing and original local-line frame refinement
are connected consumers, not claims that the historical unit-cocycle argument
was absent.

Remaining joins: prove that separately supplied original scheme-local pair
transitions become coherent over-open data under pairTransition; establish
changing-base-chart compatibility of the actual affine fppf reconstruction;
and apply the complete construction to that exact fppf datum. General fppf
line-stack effectivity, rigidifications, represented Picard/Jacobian and the
full arithmetic theorem are not asserted here.

Static binding/import/placeholder checks and audit-history self-tests are
required. No local Lean ran. Complete10 hosted replay, recursive axiom audit
and independent acceptance remain pending.
