# Explicit module-sheaf gluing on an arbitrary scheme

This baseline-only five-source draft constructs a global module sheaf from
actual local modules and transition isomorphisms. It does not assume a gluing
object, a sheafification comparison or local recovery as a premise.

The input has a family of ambient module sheaves M i and chart opens U i, with
linear transition isomorphisms on every common subopen, natural under all
restrictions and satisfying identity/cocycle laws. Only the part of M i on its
own chart is used. Direct images of modules on the charts can supply these
ambient modules; that adapter and the affine reconstruction join are not
silently included in the present theorem.

OpenModuleTransition318 constructs the actual matching-family module of
sections on every W, with Γ(X,W) acting via its original restrictions.
OpenModuleChartRecovery318 computes inverse chart comparisons from the original
transition maps and proves exact transition recovery and naturality.
OpenModulePresheaf318 bundles componentwise restriction as a genuine semilinear
presheaf of modules over the original structure sheaf.
OpenModuleSheafGluing318 glues all original local components using their actual
sheaf laws, proves the overlap transitions remain compatible, and proves
restriction and uniqueness of the resulting matching family.
OpenModuleGluedSheaf318 proves the actual global sheaf condition, recovers chart
linear isomorphisms on all subopens and actual over-site/open-subscheme sheaf
isomorphisms. Given covering rank-one chart frames, it constructs a genuine
LineSheafClass318.Line on the arbitrary original scheme.

Coverage is explicit in the line theorem. The sheaf construction itself works
without claiming the charts cover X. Empty overlaps and all subopens remain in
the input and the construction. Original scalar rings, restrictions, transition
directions and recovered objects are retained throughout.

Remaining joins: convert actual chart sheaves to ambient direct images and their
transition maps to these all-subopen linear comparisons; refine local line frames;
prove affine reconstruction compatibility across changing base charts; and apply
the resulting gluing to the actual fppf datum. General fppf line effectivity,
rigidification gluing, represented Picard/Jacobian and the full arithmetic theorem
are not asserted by this standalone gluing construction.

All five sources import only accepted baseline sources or preceding new modules.
Static source/import/hash and audit-history checks are required. No local Lean
ran. Hosted replay, recursive axiom audit and independent acceptance are pending.
