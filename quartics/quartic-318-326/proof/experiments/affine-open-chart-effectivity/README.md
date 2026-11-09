# Effective descent on original affine opens

This packet extends the frozen 83-source `affine-basechange-coherence-r3` closure by seven connected sources. It derives the affine algebraic input from an actual affine, flat, surjective scheme morphism, reconstructs on every original affine base open, constructs exact nested-chart comparisons, returns the resulting lines to the original open subschemes, and proves naturality for original compatible covering maps.

The actual ring map is `f.app U`, with algebra structure `(f.app U).hom.toAlgebra`. The source chart is the whole `f ⁻¹ᵁ U`, using `hU.preimage f`, not one chosen affine piece. Faithful flatness comes from the original Cartesian chart square and `flat_and_surjective_SpecMap_iff`. Thus no separate algebraic cover assumption is an input to the chart reconstruction.

`AffineOpenChartComparison318.comparison_cover` specifies both original reconstruction isomorphisms, the original source restriction and the actual successive/direct source pullback path. Its uniqueness follows from the original faithfully-flat affine map theorem. `OriginalAffineOpenLines318.restrictionComparison` returns these maps to the literal open subschemes and the actual `Scheme.Modules.restrictFunctor`, as required by Fi-only open gluing.

The original seven sources are:
- AffineFaithfullyFlatChart318: exact chart square and section-ring faithful flatness.
- AffineOpenChartDescent318: actual chart datum, reconstructed line, original overlap recovery, unique map descent.
- AffineOpenChartRefinement318: original section restrictions, chart squares and composition of their scheme maps.
- OriginalDescentBaseChangePath318: actual named successive/direct path is a compatible descent-data map in both directions.
- AffineOpenChartComparison318: exact reconstructed nested-chart transition, covering equation and uniqueness.
- OriginalAffineOpenLines318: original open-subscheme lines and restriction-functor comparisons.
- AffineOpenChartNaturality318: transitions are natural for original global compatible covering maps.

Remaining boundaries are substantive: composition coherence of these reconstructed nested-chart transitions, assembly of transitions on possibly non-affine pair intersections, their full triple cocycle, and global object gluing. A general fppf covering with non-affine source is not yet reduced to this affine-morphism case. No represented Picard or Jacobian assertion is made.

All predecessor bytes, including the narrow c1 TildePullback composition/identity repair in r3, are copied exactly. No local Lean compilation was run. Static source/dependency checks are not elaboration or mathematical acceptance. The entire 90-source packet still requires hosted compilation and recursive axiom audit; independent acceptance remains pending. The accepted progress snapshot is unchanged.
