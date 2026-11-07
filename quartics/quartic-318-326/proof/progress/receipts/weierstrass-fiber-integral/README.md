# Actual geometric integrality of completed Weierstrass fibers

## Proven scope

This packet proves geometric integrality and geometric connectedness of the actual completed short Weierstrass family constructed in `WeierstrassGluing318`, over every commutative base ring. There is no supplied irreducibility, integral-fiber, connectedness, or discriminant hypothesis. In particular it applies to the literal OpenJ family and its actual scheme-theoretic fibers.

1. `AffineCoordinateDomain318.coordinateEquiv` identifies the literal multivariate quotient with Mathlib's actual Weierstrass coordinate ring. Both maps, both inverse laws, and the coordinate images are proved. The existing actual Weierstrass polynomial/domain theorem then proves the literal affine ring is a domain over every domain.
2. `InfinityCoordinateDomain318.z_regular` proves the infinity-chart denominator is a non-zero-divisor in the original quotient. It uses the actual polynomial factor criterion: the defining cubic is not divisible by `z`, since setting `z=0` gives `-x^3`. Thus localization is injective. The exact previously proved overlap isomorphism identifies that localization with the affine domain localization, proving the entire original infinity ring is a domain.
3. `CompletedIntegral318.completed_integral` proves integrality of the actual glued scheme over every domain. The two open chart images are irreducible, their intersection is genuinely nonempty using the actual overlap spectrum, and they cover the whole scheme. Reducedness is local on that same actual open cover.
4. `GeometricFibers318.geometrically_integral` transports the result through the previously proved actual arbitrary-algebra Cartesian base-change square. Every morphism from a field spectrum is converted using the fully faithful Spec functor, not an assumed coefficient interpretation. Geometric connectedness follows, as do literal OpenJ and scheme-theoretic fiber results.

## Main interfaces

- `AffineCoordinateDomain318.coordinateEquiv`, `affine_domain`
- `InfinityCoordinateDomain318.z_regular`, `localization_injective`, `infinity_domain`
- `CompletedIntegral318.completed_integral`
- `GeometricFibers318.pullback_integral`, `geometrically_integral`, `geometrically_connected`
- `GeometricFibers318.literal_geometrically_integral`, `literal_fiber_integral`

## Reproduction

Run `bash build.sh`. It strictly rebuilds all four modules with `debug.skipKernelTC=false`, then recursively audits every declaration introduced by them. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The existing sibling packets listed in `run-one.sh` are dependencies, not assumed theorem interfaces.

Lean 4.35.0; Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Boundaries

Geometric integrality does not assert smoothness for singular coefficient choices. The literal OpenJ smooth/proper/relative-dimension-one properties are supplied by the separate checked chart, projective and dimension packets. This packet does not construct the full relative group law, a relative multiplication or primitive-torsion scheme, a genus/cohomology comparison, or the complete global refined geometric realization. No unconditional final Diophantine endpoint follows from this packet alone.
