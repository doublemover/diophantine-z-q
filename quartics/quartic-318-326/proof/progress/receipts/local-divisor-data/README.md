# Actual local-DVR data to finite-divisor comparison

This packet constructs the existing SourceJacobianBound318.FiniteData from actual local algebra instead of accepting its nonexceptional coefficient inequality.

`LocalExtension` carries actual rings and fields, fraction-field towers, integral closure, finite separability, DVR structures and an actual uniformizer. Its values are Mathlib's actual different exponent and actual normalized DVR valuations.

`HorizontalData` gives residue characteristic zero and the actual canonical/pullback coefficient identifications, allowing the nonnegative canonical correction at infinity. `VerticalData` gives actual positive residue characteristic, local-degree and branch-prime restrictions, and the coefficient identifications. `CoefficientData` also allows the unramified zero-coefficient case. Its bound theorem derives domination using the already-proved actual different and ramification theorems.

`ModelData` replaces the prior local_domination inequality with these actual local certificates. `ModelData.toFiniteData` constructs the exact frozen finite-divisor record and proves the missing inequality. `ModelData.bound` returns the actual canonical-section bound3h(1/n)+2log(6N)log(d)/log2.

This is an input-construction theorem, not a claim that the algebraic-geometric model has been constructed. The actual completed local fields, identification of canonical/pullback coefficients, unramified zero coefficients, intersection matrix, adjunction and section projection remain explicit model data. The negative-definite matrix itself is not proved for a specific resolution here. No global GeometricRealization or unconditional FiveContact49Height is asserted. Most audited declarations are structure projections, and their count is not a measure of mathematical completion.

Run `bash run.sh` for a fresh strict-kernel build and exhaustive axiom audit. Dependencies include the frozen386-module checkpoint, local-different-bridge, residue-different-bridge and vertical-residue-bridge; no frozen source is changed.
