# Independent review: actual Weierstrass surjectivity and group addition

Accepted at the stated scope. The two surjectivity modules and nine addition modules were copied exactly and freshly kernel-compiled. Their exhaustive project audits passed 20 and 48 declarations respectively, with only propext, Classical.choice and Quot.sound. All copied source hashes were checked against the frozen originals after replay.

## Surjectivity

If ℘ omits c off its actual period lattice, the reciprocal 1/(℘−c), defined to be zero on the lattice, is entire. The removable expression at zero is explicitly z²/(1+z²(℘Except−c)); periodicity transports it to every lattice point. Actual lattice compactness makes its range bounded, and Liouville makes it constant. Its zero at the lattice contradicts its nonzero value at the actual half period. Thus every c is attained off the lattice. The differential equation and replacing z by −z supply the correct ordinate, including ordinate zero. Infinity is covered by a lattice argument. No degree-two or surjectivity theorem is assumed.

## Ordinary chords

The rational chord expressions are checked by Lean field arithmetic against the actual cubic and differentiated using the genuine ℘ second-order ODE. An initial translate is constructed from the just-proved pair surjectivity. Analytic quadratic-ODE germ uniqueness proves local agreement; actual meromorphic continuation propagates it. At −w, the numerator of the chord slope is nonzero and the denominator has a simple zero whenever ℘'(w) is nonzero. The resulting actual order−2 pole forces the translate to be w modulo the lattice. The argument uses punctured equality at poles and continuity only at ordinary evaluation points.

The normalized x and y coordinates use the exact (2π)² and 2(2π)³ scalings. Their slope and reflected ordinate are bound to Mathlib's actual affine Point.add operation, including its sign convention. The symbolic scratch script is provenance only: the identities are proved by kernel-checked field arithmetic.

## Exceptional branches and final equivalence

Actual ℘ value fibers are countable by the previously checked pair injectivity and the two possible ordinate signs. Derivative zeros are contained in the actual half-lattice preimage. The union of the seven exceptional conditions is countable, so an auxiliary complex argument exists. Three ordinary chord identities and actual group associativity/right cancellation then handle every remaining finite tangent and two-torsion case. Lattice arguments and inverse pairs are treated directly. Hence point_add is genuinely unconditional, and the final torusAddEquiv is an actual additive equivalence, not a type bijection relabeled as a group equivalence.

## Remaining scope

These modules do not yet prove analytic/manifold compatibility or identify a separately specified modular family/fiber with the normalized model. The earlier pair-injectivity, lattice/Eisenstein and normalized-curve dependencies have separate scoped reviews. The current replay reuses their checked oleans and Mathlib dependencies; it does not recompile all upstream sources.

Run `bash run.sh` in this directory. Copied project sources are first on LEAN_PATH, and the addition replay consumes the copied surjectivity modules.
