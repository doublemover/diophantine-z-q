# Actual affine descent maps and transitions

This61-source draft joins genuine categorical-double descent data and their
original covering sheaf maps to the retained unique affine reconstruction maps.
Three new sources prove transport of arbitrary overlap intertwiners, derive the
exact tensor data and intertwiners from actual scheme data, and construct unique
base maps with the displayed pullback comparison square. Identities, composition,
isomorphisms from specified inverse pairs and exact transition cocycles descend.

All58 predecessor source files are byte-identical to actual-affine-overlap-
effectivity, including its typed coordinate repair. No previous packet is edited.
ActualAffineDescentData318.Datum contains only the original line, actual double
sheaf overlap and actual diagonal/triple equations. Hom contains only the actual
cover sheaf map and its actual double compatibility square. Tensor and module
laws are derived. The new map consumer uses the original reconstructed line and
comparison from ActualAffineLineReconstruction318, with no fresh object choice.

This supplies genuine affine transition maps from actual geometric data. It is
not a proof that arbitrary affine base changes commute with reconstruction or
that non-affine local objects glue. Those constructions, general fppf coverings,
rigidifications and represented Picard/Jacobian remain further work.

Static hash/import/placeholder checks and audit-history self-tests are required.
No local Lean ran. Complete61-source hosted replay, recursive axiom audit and
independent acceptance remain pending. No full arithmetic theorem is claimed.

## Revision r2: retain original scalar action

Run42582121938 at c4cd4ae passes16 predecessors, then rejects the attempted ordinary tensor change because Algebra.toModule is not the original ExtendScalars Module.compHom action. This revision removes that conversion and finishes the unchanged scalar multiplication equality directly by rfl, exactly as pinned ModuleCat.ExtendScalars.smul_tmul is proved. Sixty sources remain byte-identical, all statements/hypotheses are unchanged, and exact failed bytes/evidence are retained. Hosted61 replay/audit remains pending; no local Lean ran.

## Revision r3: retain original geometric law inputs

Source review found that effective uses the existing hdiag/htriple section hypotheses only in its construction proof. This revision binds those already supplied original laws explicitly in the theorem signature. Sixty sources remain byte-identical to r2, including its retained exact scalar-action repair. This is a preemptive source-level fix, not a newly observed hosted failure. Full61 hosted replay/audit remains pending; no local Lean ran.

## Revision r4: bounded original triple normalization

Run42584029818 at c7d3bc3 passes17 sources, including the exact scalar-action repair. The next coassociativity proof hits maxRecDepth while re-elaborating the deeply nested original tensor/comparison target. This revision uses the exact ModuleCat.comp_apply equation instead of restating the complete target, with a bounded maxRecDepth3500. The original heartbeat cap, all maps, statements and hypotheses are unchanged. Sixty r3 sources, including explicit geometric law theorem binders, remain byte-identical. Exact hosted failure is retained; full61 hosted replay/audit remains pending and no local Lean ran.

## Fresh revision after exact8b hosted failure

Rewrite the evaluated cocycle hypothesis by the exact original homEquiv_value equation in reverse before using it as the coassociativity proof. This replaces unsuccessful target-side simplification and preserves all actual tensor maps, scalar structures and hypotheses. Frozen predecessor and tested failure bytes remain unchanged. Full hosted compile and audit pending.
