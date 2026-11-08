# Intrinsic Omega on actual open charts

This isolated packet proves that intrinsic relative differentials commute with actual open restriction, then identifies intrinsic global Omega on the actual Weierstrass charts and at the actual identity. It does not edit the shared repository or earlier frozen packets.

## Construction

`DerivationOpenRestriction318` restricts coefficients and sheaf-valued derivations through the genuine regular-function isomorphisms of an open immersion. It also constructs the reverse pushforward of derivations, using actual structure-sheaf maps.

`IntrinsicOpenRestriction318` proves the full universal property for the restriction of intrinsic Omega. Its descent map is formed from ambient intrinsic universality, actual module restriction, and the actual restriction/pushforward adjunction counit. Existence and uniqueness are proved on every module sheaf. The resulting isomorphism commutes with the actual universal derivation. There is no assumption that Omega is quasi-coherent, locally free, or compatible with restriction.

`FamilyOpenRestriction318` identifies these restricted coefficients with the exact composite scheme structure map. It expresses the result both as actual restriction and actual pullback, and combines it with the proved intrinsic affine comparison.

`IntrinsicFamilyFrames318` proves the structural maps of the actual x, finite, and infinity charts and identifies restriction of the actual global family Omega with each ordinary tilde Kähler sheaf. Therefore the intrinsic differential sheaf is locally a line on the smooth family, and agrees locally with the earlier normalized invariant line on the actual covering charts.

`IntrinsicIdentityFrame318` proves that the actual pullback of intrinsic global Omega to the actual infinity identity is the previously constructed infinity-chart cotangent line. In particular that intrinsic identity cotangent sheaf is genuinely free of rank one over the base. No global Hodge-map isomorphism is assumed.

## Exact boundary

The packet does not yet glue the three normalized intrinsic chart identifications into one global Omega frame. Compatibility with the canonical differential transition maps must be carried through the new intrinsic comparison and the existing full-overlap equalities. It therefore does not prove unconditional invertibility of the canonical Hodge-to-identity map. Actual regular-function descent is being proved in a separate packet.

No compact modular/PEL base canonical or bicanonical comparison, analytic or metric comparison, global-source realization, or unconditional arithmetic soundness theorem is asserted.

## Verification

`bash verify.sh` takes the shared exclusive heavy-compilation lock, strictly rebuilds every module with `debug.skipKernelTC=false`, and recursively audits all declarations. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted. `python3 create-receipt.py` freezes source/log hashes after the successful audit. No new Mathlib source copies are introduced.
