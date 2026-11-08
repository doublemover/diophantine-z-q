# Whole relative infinity-input addition

This packet constructs the actual addition morphism on the entire relative product of the two infinity charts, over every commutative coefficient ring with unit short-Weierstrass discriminant.

The three principal opens D(V1), D(V2), and D(domainElement) cover the whole product. The first two use the whole mixed-input addition laws, and the third uses the regular both-infinity law. All overlaps are actual Scheme morphism equalities, including arbitrary nonreduced coefficient algebras.

Key endpoints:

- `BothFiniteGlobalResolved318.scheme_agreement` and `BothFiniteReversed318.scheme_agreement`: whole finite-input comparisons, in both input orders.
- `BothMixedWholeComparison318.direct_agreement` and `.reversed_agreement`: whole mixed-input comparisons.
- `MixedAdditionExchange318.scheme_agreement`: exact exchanged mixed-input compatibility.
- `BothInfinityLocal318.local_agreement`: all three tensor-product overlaps.
- `WholeBothInfinity318.coordinateAddition` and `.addition`: the glued coordinate and actual relative fiber-product morphisms.
- `WholeBothInfinity318.coordinate_restriction`, `.restriction`, and `.regular_restriction`: all local restrictions.
- `WholeBothInfinity318.coordinate_over_base` and `.addition_over_base`: base compatibility.
- `WholeBothInfinity318.origin_output`: the actual pair of infinity sections maps to infinity.

`MixedAdditionExchange318.scheme_agreement` retains its fully inferred proof type as a proof-valued definition. It is an actual equality proof and is used in subsequent explicitly typed Scheme-equality theorems. Restating its redundant concrete signature triggered kernel normalization of large tensor/localization instances. Full kernel checking is enabled throughout.

The generic complete-localization-cover helper is copied unchanged from the checkpoint lane. No field-point equality, reducedness, density premise, assumed group structure, or extra axiom replaces a Scheme morphism comparison.

Scope remaining: glue the four whole input-chart laws over the completed relative curve; prove global group axioms; construct the certified multiplication-by-N and relative primitive torsion kernels. This packet does not claim those global endpoints.

Run `bash run.sh`. It holds the shared compile lock, sequentially replays the listed modules, and recursively audits every new declaration. Allowed axioms are only propext, Classical.choice, and Quot.sound.
