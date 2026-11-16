# An alternative integral affine model without inverted primes

For each original rational twist c_i, let d_i be its positive integer denominator and n_i its signed numerator. The proposed model is the monic four-root tensor order over Z[T] with radicands n_i*d_i*(T-contact_i). This construction requires no inverted separation integer and no unit twists on the integral base.

It is finite free of rank16 over Z[T]. After rational base change, d_i becomes a unit and scaling the i-th root by d_i gives an explicitly constructed algebra equivalence with the original ContactKummerOrder318.SourceOrder c. The comparison is proved from n_i/d_i=c_i, not postulated. The candidate additionally embeds this integral order into that same source, proving it is a domain by faithful scalar extension.

This avoids the no-map obstruction because the new base is Z[T], not Z[1/denominator(c)][T]. It is a concrete alternative affine order, not yet the required geometric solution: a proper model, normalization or resolution, bad-fiber geometry, extension of the original differential-square sections, and their integral generation/KS comparison remain unproved. In particular finite flatness of this monic cover does not imply smoothness in residual characteristic2 or at colliding contacts.

No current consumer, assumption or accepted source is changed. Source candidates only; independent review and hosted Lean required.

# Why the existing good-place model cannot extend by the same base map

The source constructs the converse to ContactFinitePlaceBaseMap318.baseMap: a unital ring map from the actual arithmetic base Z[1/denominator(c)] into a finite-place integer ring exists if and only if the denominator has norm one. In particular no such map exists at an excluded place. The proof uses actual unit and inverse integer bounds, not a geometric assumption.

This rules out trying to delete the good-place premise from the existing localized-model construction. It does not rule out a different integral model, semistable alteration, or bad-place cotangent/dualizing comparison. Those constructions, including how the J²-scaled sections generate or fail to generate their lattices, remain necessary and unproved. IntegralScaledCoefficientUnits318 explicitly relies on J being a unit to show primitivity; at excluded primes that proof cannot be reused.

Candidate only: independent source review and hosted Lean are required. No local Lean.


# Explicit nonreduced fibers of the integer affine model

An explicit tensor basis proves each original root remains nonzero, even when its radicand vanishes. Its known square relation then gives a nonzero square-zero element. FourRootOrder.baseChange transports that witness into the literal scalar-extension fiber.

For OriginalIntegerAffineModel318, this applies when the image of one cleared coefficient num(c_i)*den(c_i) is zero. A sufficient condition is that the denominator becomes zero in the target ring. These are explicit hypotheses, not claims at all excluded primes. The construction is valid over any nontrivial commutative target ring, not only fields.

Finite-free/domain properties of the total space do not imply reduced or smooth fibers. This calculation identifies genuine bad-fiber structure in the proposed model; it does not construct normalization, a regular/proper model, sections on a dualizing sheaf or a KS identification. Such geometry remains to be proved. No local Lean.


# Reciprocal chart for the integral affine model

Finite chart y_i²=d_i(t-a_i); reciprocal chart z_i²=d_i*s*(1-a_i*s). Both are monic four-root tensor orders finite free rank16. On any overlap where s is a unit, the coefficient identity t=s^-1,z_i=s*y_i yields a constructed algebra equivalence using exact root scalings. No d_i or integer prime is inverted.

The specialization d_i=num(c_i)*den(c_i), a_i=original integer contacts uses exactly the earlier integer affine model. This is a concrete chart/transition bridge toward a proper finite cover of P1, but there is not yet a glued scheme, cocycle/open-immersion proof, global finite/proper morphism, normalization, smoothness, or bad-place cotangent-generation theorem.

Source candidates only. No local Lean.

## Hosted integration

This packet is an additive successor of height-original-ks-lattice-assembly-r25 at a3111432428ac6fa4ea482a6b9dd3ac26122837a: all 177 predecessor roots byte-identical and ordered identically, followed by seven independently source-reviewed new modules. No current consumer is changed. The integer affine model has an explicit rational-fiber equivalence, specified fibers have proved nonzero square-zero witnesses, and reciprocal charts have an algebraic transition. There is no glued scheme, properness, normality or cotangent-generation claim. The no-base-map theorem concerns only the previous localized base. The210 KS identification remains unproved.

Only the KS registry slot changes; all other15 active slots and workflow/budgets remain unchanged. Existing Progress Lean experiments checks each root and recursive declaration audit. No acceptance, kernel pass or global realization claim is made before hosted results. Historical predecessor metadata remains in its original immutable packet rather than copied evidence trees.
