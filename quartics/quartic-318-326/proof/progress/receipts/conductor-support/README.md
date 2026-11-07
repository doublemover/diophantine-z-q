# Conductor support and actual character-index bridge

This packet has two strictly kernel-checked Lean modules, 12 public theorems and 15 recursively audited declarations, plus an independent mathematical conductor/primitive-contact review.

- `NebentypusOrder318.character_pow` and `character_order_dvd` derive the exact2*card(Q) exponent/order bound from a character whose square is trivial on the kernel of an actual homomorphism to a finite group.
- `determinant_square` obtains that premise by cancelling the cyclotomic factor in the actual determinant-square relation.
- `kernel_index_le_of_pow` is the essential extra step: for a field-valued character it injects the image into actual roots of unity. Therefore the kernel index, not only the character exponent, is bounded. An exponent bound alone would not suffice for an arbitrary commutative target group.
- `determinant_finite_index_bound` transports through a surjective quotient to the actual finite Dirichlet-character kernel and proves its index is at most4608R when the finite restriction group has cardinality at most2304R.
- `ModularIndex318.index_from_determinant` composes this with the independently reviewed actual Euler product. `jacobian_growth_from_determinant` feeds the resulting index bound to the actual log(6dN) estimate and49/8 growth theorem. Both the free character-order bound and free numerical index bound have been removed.

The arithmetic-geometric inputs remain explicit: the actual quotient maps/characters and determinant identity, controlled field degree, conductor support/level, actual modular degree formula, and the actual analytic Jacobian-height inequality. These modules do not fabricate the associated Shimura/modular curve or claim FiveContact49Height.

`CONDUCTOR-REVIEW.md` independently traces the integral tame quotient, exact R=badProduct*radical, primitive detector coordinates, sign cochain, potential good reduction, Pan prime5 theorem, same-form coefficient-prime3 switch, Casselman/Carayol normalization, local ramification budget, and nebentypus kernel index. It distinguishes mathematical theorem applications from Lean constructions. The corrected CM surface-to-contact packet is explicitly identified.

Run `bash conductor-support/build.sh` from the workspace. It rebuilds both modules, recursively checks every declaration's axiom roots, and runs the exact Python/Fraction constant/contact check. Only propext, Classical.choice and Quot.sound are permitted. The receipt hashes local sources, logs, and inspected primary files; web-only sources are recorded by their exact version URL rather than an invented file hash. No Git or repository files are modified.
