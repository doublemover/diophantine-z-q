# Original affine-chart composition coherence

This 96-source packet retains all 90 frozen `affine-open-chart-effectivity` sources and adds six connected composition consumers. It closes the prior nested-chart coherence boundary, first on the reconstructed spectrum lines, then on the literal original open subschemes and their actual restriction functors.

`AffineOpenChartComposition318.composition` proves that successive reconstructed chart transitions equal the direct transition composed with the original base pullback path. It compares the actual sheaf maps after the original faithfully-flat cover and the specified reconstruction comparison. The proof uses the original cover-comparison pasting, source-line associativity and naturality. No transition composition law is an additional input on the global descent datum.

`OriginalOpenPullbackComposition318.composition` transports this equality through the original affine-open isomorphisms. `OriginalOpenRestrictionComposition318.composition` then supplies the exact Fi-only restriction-functor equation, using accepted `RestrictionPullbackCoherence318.composition` and the original named open inclusion composition.

Six new sources:
- CanonicalCoverPastingInverse318: inverse form of the original covering-path pasting law.
- AffineOpenChartComposition318: faithful-cover proof of reconstructed nested-chart composition.
- SheafComparisonPasting318: original commuting-square comparisons transport a proved transition equation.
- OriginalOpenPullbackComposition318: actual open-subscheme pullback transitions compose.
- RestrictionTransitionPasting318: actual adjunction-normalized restriction/pullback comparisons transport this law.
- OriginalOpenRestrictionComposition318: actual original restriction comparisons satisfy the nested-chart equation.

Still separate: extension to possibly non-affine pair intersections, actual pair/triple gluing data on a covering family, global effective descent and non-affine fppf sources. No represented Picard/Jacobian or full arithmetic conclusion is asserted.

No local Lean build was run. Source/dependency checks and the audit-history self-test are structural only. Hosted compilation, recursive axiom audit and independent acceptance remain pending. Frozen predecessor evidence and the accepted progress snapshot remain unchanged.

## Revision after exact1ca04ec hosted replay

After the generated NatTrans.ext reduces to equality of app functions, use funext rather than intro. Pin the tilde component to the exact original bundled coefficient ring R in the component theorem, preventing re-inference of a reconstructed CommRingCat carrier through ModuleCat. Carry the same typed normalization into the following identity theorem. No original map, scalar or statement scope is replaced; retain the entire passing prefix and exact1ca evidence. Frozen predecessors and exact failure bytes are preserved. Hosted validation pending.
