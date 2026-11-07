# Actual complete Weierstrass family base change

This packet proves arbitrary coefficient base change for the actual completed two-chart Weierstrass Scheme. It provides a genuine Scheme fiber-product isomorphism, not just a bijection of field-valued points.

## Checked objects and maps

1. `InfinityBaseChange318.baseChangeEquiv` identifies the actual tensor product S tensor_R (R[x,z]/(z-x³-Axz²-Bz³)) with the literal infinity-chart quotient over S and mapped coefficients. Both inverse laws and generator images are proved. `schemeIso` is the actual affine Scheme pullback isomorphism, with both projection identities.
2. `WeierstrassCoefficientMap318` constructs the actual localization map on the shared overlap and checks both coordinate maps, including the inverse of z. Exact finite and infinity overlap identities give the actual global coefficient morphism by the original pushout universal property. It commutes with the original base maps and preserves the actual infinity section.
3. `WeierstrassBaseChange318` proves the global coefficient morphism has exactly the expected finite/infinity open-chart inverse images. These are actual Cartesian chart squares. The known affine and newly proved infinity tensor pullbacks are then transported through an actual two-chart open cover. `coefficient_base_pullback` proves the entire coefficient square is Cartesian.

Main API:

- `WeierstrassBaseChange318.schemeIso A B`: the actual pullback of the completed family along Spec S to Spec R is isomorphic to the complete cubic over S with coefficients mapped from A and B.
- `schemeIso_inv_base` and `schemeIso_inv_curve`: both projections are the prescribed actual maps.
- `literalFiberIso N T`: exact specialization to the entire literal OpenJ family at any commutative coefficient algebra T.
- `WeierstrassCoefficientMap318.coefficientMap_infinity`: the distinguished section is preserved.

These statements hold over arbitrary commutative base rings and arbitrary commutative algebras. No field, flatness, reducedness, discriminant-unit, supplied overlap-identification or supplied fiber-isomorphism hypothesis is used. Smoothness and properness remain the independently proved properties of the same actual family.

## Replay and boundary

Run `bash completed-base-change/build.sh`. It explicitly lists project dependencies, rebuilds all three modules with kernel checking enabled, and recursively audits all their declarations against only the standard three Lean axioms. Source and build hashes are recorded in the receipt.

This packet does not assert a relative elliptic group law, a relative multiplication/torsion morphism, a primitive-torsion cover or the complete global refined geometric realization. The complete field-point equivalence and the proper/separated cubic are separately frozen and reviewed.
