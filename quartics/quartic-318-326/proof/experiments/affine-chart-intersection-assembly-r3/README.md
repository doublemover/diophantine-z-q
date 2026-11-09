# Original non-affine intersection assembly and global line

This127-source packet joins the exact98-source `affine-basis-morphism-extension-r2` closure and the exact23-source `local-chart-categorical-descent-r8` closure, then adds six connected geometric consumers.

For an actual affine, flat, surjective morphism f:X→Y and original geometric line descent datum, the earlier sources reconstruct an original line on each affine open of Y. The new sources derive its canonical pair transitions on every common open, including non-affine intersections, with genuine restriction compatibility and the original triple cocycle. These are fed into the existing actual open-cover gluing construction to produce an actual global `Line Y` with explicit recovery of each original affine-chart reconstruction.

No separatedness, quasi-compactness, finiteness of the chart cover or affineness of intersections is assumed. The index set is the entire original affine-open basis. Open-image coefficient actions are the actual inverse appIso actions from Scheme.Modules.restrict, checked explicitly when extending the component isomorphisms.

New sources:
- AffineChartAmbientComparison318: original direct-image/counit chart comparisons and their proved restriction law.
- AffineChartLocalPairs318: exact affine common-subchart pair maps, restriction compatibility and cocycle.
- AffineSubopenIsoExtension318: original over-open affine component isos extend to a whole-open actual sheaf iso using the full affine basis and original restricted scalar actions.
- ActualChartPairExtension318: the exact reconstructed chart pairs on arbitrary common opens and their whole-open cocycle.
- ActualChartPairRestriction318: arbitrary-open restriction compatibility, retaining original image-equality section transports.
- AffineMorphismGlobalLine318: full-cover actual transition data, actual global framed line and explicit original affine local recovery.

The final effectivity endpoint is still separate: constructing the global isomorphism f*line≅the original covering line and proving its original categorical-double compatibility. The current global line is not advertised as satisfying an unproved global covering square. General fppf sources that are not affine morphisms and represented Picard/Jacobian remain separate.

No local Lean build was run. Static source/dependency/hash checks and the audit-history self-test do not constitute elaboration or mathematical acceptance. Hosted compilation and recursive axiom audit are pending, and the accepted progress snapshot remains unchanged.

## Revision after exact36f5b5e-replay hosted replay

Use the exact original tilde functor object in the canonical comparison component statements, rather than an elaborated tilde wrapper with opaque localization instance normalization. The whole natural-transformation composition theorem already passes in the exact36f5b5e replay. Carry the same object expression through inverse composition and its two immediate original-line consumers; no map, coefficient ring, hypothesis or coherence assertion is changed. Frozen predecessors and exact failure bytes are preserved. Hosted validation pending.

## Revision after exact204e9b7 hosted replay

Expose exact original over-open component composition and identity as reusable typed lemmas before building sectionData. Use those laws directly on the original categorical cocycle equality, instead of whnf-normalizing the entire dependent gluing datum in a large change tactic. Preserve the first five hosted passing open modules and all existing maps; no heartbeat increase or statement weakening. Frozen predecessors and exact failure bytes are preserved. Hosted validation pending.
