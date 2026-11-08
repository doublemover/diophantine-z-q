# Actual finite-addition zero fiber

The entire zero fiber of the actual finite-input addition law is isomorphic to the actual affine curve by its anti-diagonal. This is an equality of schemes with explicit inverse morphisms over every commutative coefficient ring with unit discriminant, including nonreduced rings.

Endpoints:
- `InfinityOutputZero318.input_maps`: either infinity-output chart has zero output only when its actual two finite input algebra maps are negatives.
- `FiniteLocalZero318.input_maps`: exact four-chart version; the two finite-output cases force the test ring to be the zero ring.
- `FiniteZeroScheme318.coordinate_zero`: descent along the actual pulled-back four-open cover for arbitrary Scheme tests.
- `FiniteAdditionZero318.zero_iff` and `zero_iff_antiDiagonal`: whole relative finite-product criterion and exact factorization.
- `FiniteAdditionZeroFiber318.iso`: explicit actual zero-fiber isomorphism, with `toFiber`, `fromFiber`, both projection identities, and both inverse identities.

The nilpotent-safe local step uses the unit homogeneous numerator V: output zero implies U*d=0 and d^3=0, then V*d=0, hence d=0. It does not infer d=0 merely from d^3=0. The remaining numerator is a unit, and the two exact curve equations force the other anti-diagonal coordinate.

All five sources passed first-time strict kernel checks; their recursive audit passed 58 declarations, with only propext, Classical.choice and Quot.sound. No local full-chain replay was run. Hosted integration and independent review remain separate.

Not claimed: a full completed-curve zero-fiber identification, the full tripling kernel, any zero-section/complement decomposition, general-base associativity, PEL identification, or the final arithmetic witness construction.
