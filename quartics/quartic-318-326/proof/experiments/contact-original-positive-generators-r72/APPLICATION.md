# OriginalAffineLineSectionLifting318: explicit universe for the same singleton retract

## Exact observed scope

Hosted run 43575728180, head d97d209a1666cdcb0d7ae2488523fbfa7d46fae6, positive r71 own artifact 14106389133 first fails OriginalAffineLineSectionLifting318 (4.931s). Its prior OriginalAffineLineLocalHOne318 repair passes (4.228s), and OriginalLineRestrictionAdditive318 passes (1.569s). All three displayed errors are unresolved PUnit universe levels in the same finite-retract application at lines22-23; no later failure is inferred.

## Required inputs and actual construction

ExtFiniteRetractVanishing318.eq_zero requires a finite index type, objects N indexed by it, morphisms out and back with complete sum out_i ≫ back_i = identity of M, and vanishing of every Ext class through every N_i. Here M is the actual kernel S.X₁ of the original short exact sequence on Spec R. The original construction uses a singleton family constantly equal to OriginalLineRestrictionAdditive318.additive L; its maps are exactly e.hom and e.inv, where e identifies that kernel with the original additive line.

The sole source change is PUnit to PUnit.{1} in the family binder, explicitly selecting the small singleton type Type 0. The original statement left this index universe unconstrained, causing all three binder errors. The complete singleton is retained; no index is omitted, no family becomes empty, and no replacement object is introduced. The same finite sum and (by simp) identity proof through e.hom ≫ e.inv are unchanged. The morphism lambdas obtain their index from that same now-unambiguous family.

## Object, scalar, map and local-condition parity

All original sheaves and morphisms remain untouched. The exact boundary class is y.comp hS.extClass with y = (zeroEquiv S.X₃ ⊤).symm s, and its target is the original kernel Ext group. The vanishing input remains OriginalAffineLineLocalHOne318.eq_zero R L ⊤ (isAffineOpen_top _) z for every class z of the original line. The original scalar action is forgotten only via the unchanged additive identification; there is no new scalar restriction, chart, open, transition, base change or global trivialization.

Every R : CommRingCat.{0} with IsDomain R, every original line L, every short exact S with its exact e, and every section s over the original top open remain quantified. The long-exact-sequence application Ext.covariant_sequence_exact₃, zeroEquiv_naturality conversion, chosen lift and final equality are unchanged. No new nonzero, rank-one, triviality or selected-section hypothesis is added.

## Actual direct consumer

OriginalLineOpenSectionLifting318.surjective_image directly applies this exact surjective theorem to the actual pulled-back line LineSheafPullback318.line f L, the mapped short complex S.map F, its mapped short-exactness proof, and F.mapIso e composed with the original pullbackIso. Its original surjective_affine subsequently handles both nonempty and empty affine opens. Those statements, restrictions, full open domains and maps are unchanged. The direct consumer and exact finite-retract/local-vanishing producers are retained as primary source evidence, not merely an importing module.

## Review boundary

The 107-module ordered closure is unchanged; only the singleton universe annotation in one source changes, and the other106 roots are byte-identical. Imports, resource limits, transparency options, all theorem statements and all remaining proof text are unchanged. This is a source-level universe-elaboration repair requiring distinct review and hosted Lean; no local Lean/Lake, kernel acceptance, recursive-axiom audit or full arithmetic theorem claim is made.
