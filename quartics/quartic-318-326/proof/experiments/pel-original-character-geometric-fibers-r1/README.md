# Original scheme-point fibers and quotient topology

Six connected modules bridge the prime-ideal result to actual scheme points and produce descended domain opens for maps to arbitrary target schemes.

1. AffineOpenPointTransport uses the ACTUAL IsAffineOpen.fromSpec and its native SpecMap_appLE_fromSpec square. It supplies all-point coverage, injection and exact compatibility of app/appLE with scheme maps.
2. SpectrumPrimeOrbits converts original prime-ideal transitivity to the correct contravariant Spec direction. The inverse kernel element is explicit: pointwise ideal action is comap by inverse ring automorphism, not map by the same element without justification.
3. AffineFiberOrbits takes an actual target affine U. Finiteness supplies affineness of the FULL inverse image, not a smaller chart. Both source points are represented by the exact native fromSpec; target fromSpec injectivity identifies their actual contractions. The actual scheme-action appLE square then transports the Spec orbit back to the original source scheme.
4. GeometricFiberOrbits uses the already produced original normal affine basis to cover every target point. Thus EVERY actual fiber, including generic/nonclosed and infinity points, is exactly an original-kernel orbit. Converse uses the unchanged whole_deck_square.
5. QuotientTopology uses the proved finite/closed/surjective whole morphism to obtain the underlying quotient map. Kernel-stable subsets are genuinely fiber-saturated by the new orbit theorem; stable OPEN subsets therefore have open images.
6. For a kernel-invariant map g into an ARBITRARY scheme Z, every inverse-image open g⁻¹V is stable. descendedOpen is its actual image under the original character map, with PRODUCED openness, exact full preimage g⁻¹V and monotonicity. These are the exact domain opens needed by subsequent local factorization and gluing, not an assumed quotient topology.

Boundary: arbitrary-target local scheme maps have NOT yet been constructed/glued. This batch proves actual fibers/orbits, quotient topology and descended open domains; the categorical scheme-valued universal property still only covers affine targets from the prior batch. No numerical j or final PEL conclusion. All1120 predecessor files are exact; no local Lean or budget change. Distinct source review and hosted kernel verification remain separate.
