# Source H1 in the original explicit affine-ring coordinates

This is an uncompiled 36-module continuation: 34 exact sources from the pending
`source-mayer-vietoris-kernel-r1` packet, plus two new modules. No local Lean
compilation or recursive axiom audit was run. No strict verification or independent
acceptance is claimed for this continuation or its pending kernel predecessor.
Exact copied sources and predecessor metadata are pinned in `COPY_BINDINGS.json`.

## Concrete step toward dimension and spanning

The previous quotient uses actual sheaf sections on the full finite/infinity
intersection. This packet identifies those sections with the original explicit
rings, and proves that their original algebra maps are the actual restrictions.

- Finite ring: `ContactKummerOrder318.SourceOrder SourceTwistArithmetic318.units`.
- Infinity ring: `InfinityOpenChart318.OpenOrder SourceTwistArithmetic318.units`.
- Overlap ring: `ContactKummerOrder318.OpenOrder SourceTwistArithmetic318.units`.
- Finite-to-overlap map: `SourceOpenFractionField318.orderToOpen`.
- Infinity-to-overlap map: `InfinityOverlapLocalization318.toOpen`.

`ActualSourceHOneCoordinates318.boundary` sends an element of that actual overlap
ring to its original global H1 boundary class. Its claimed kernel is exactly all
expressions `orderToOpen a - toOpen b`. The quotient equivalence uses that literal
additive subgroup, and its representative theorem identifies the image with the
original boundary, not an arbitrary isomorphism. No dimension-five hypothesis,
Serre duality, Picard tangent identification or artificial H1 carrier is used.

## The genuine geometry-to-coordinate join

`AffineChartRingSections318.equivalence` is the inverse of the original open
immersion's `appIso` followed by the original affine `GammaSpecIso`. It is an
additive equivalence, not an assigned new group structure. `equivalenceOn` only
transports across a proved equality of opens.

The exact whole intersection theorem is
`ContactFullOverlap318.actual_full_intersection`. It identifies the full finite
and infinity chart intersection with the image of the original unbranched source
open. `ContactOverlapMaps318.source_square` and `infinity_square` identify both
actual scheme routes to that same source open. Their original open-immersion
instances and `OpenChartSections318.affine_restriction` prove both restriction
compatibilities. Thus neither a dense-open shortcut nor a generic-field
identification substitutes for the full-overlap comparison.

Kernel transport uses the original section-kernel theorem, surjectivity of both
chart section equivalences and injectivity of the overlap section equivalence.
This accounts for *every* pair of section representatives. The final quotient
map is the first-isomorphism map of the original boundary composed with the exact
overlap coordinate equivalence.

## Remaining work

This makes the next dimension/spanning calculation a concrete ring problem:
reduce the original localized four-root overlap ring modulo the images of the
original finite and infinity rings, then identify the surviving classes with the
five actual quotient pullbacks. That reduction and pullback compatibility are not
proved here. In particular, neither the 16-term Kummer ring basis nor the separate
five-dimensional differential basis alone computes this H1 quotient.

The new sources remain subject to hosted strict-module elaboration and kernel
checking. Open-equality transport, chart-image definitional equalities, and the
explicit kernel witness conversions are the primary elaboration risks. Shared
experiment activation and source admission remain coordinated separately.
