# Minimal local lattice of the original contact sections

New proof candidate on the KS metric construction path, based on exact source APIs at ba417446. No local Lean, no hosted verification, no publication.

FinitePlaceTwoSectionLattice318 constructs a principal valuation-ring lattice from two actual field values by choosing the one with maximum valuation. For a nonzero first section it proves both memberships, universal minimality among all embedded integral submodules, and equality with their literal two-generator span. It computes the local norm exactly, not by manufacturing a Hodge metric.

OriginalMinimalExcludedSections318 applies this to the original J²-scaled contact section values. The existing a0_ne theorem supplies nonvanishing. It constructs ExcludedGenerators with no supplied bad-place generator, and proves every other such lattice contains it. Equality with an actual geometric lattice still requires genuine generation by the two original sections.

This removes the *bare existence* of the weak ExcludedGenerators record as an assumption. It does not prove this lattice is the actual bad-prime cotangent/dualizing lattice, that original sections generate that geometric lattice at all excluded places, or that its 210 image is the square of an independently constructed Hodge lattice. Those are real missing geometric assertions. No GeometricRealization, PEL/Jacobian identification, local KS identity or full height bound is claimed.

Integration should first replay these two modules after the existing KS lane producers, then independently review any consumer using minimalGenerators. Do not silently substitute this object for an actual geometric lattice in a KS claim.

## Hosted integration

This packet is an additive successor of height-original-ks-lattice-assembly-r23 at 6d6685ae8384ce685ab16c83b0098e842cc1e933: all 173 predecessor roots byte-identical and ordered identically, followed by the two new modules. No current consumer is changed to use minimalGenerators. Actual geometric lattice generation remains an explicit hypothesis of equal_of_generated, and cotangent/dualizing provenance and the210 KS identification are still unproved.

Only the KS registry slot changes; all other15 active slots and workflow/budgets remain unchanged. Existing Progress Lean experiments checks each root and recursive declaration audit. No acceptance, kernel pass or global realization claim is made before hosted results. Historical predecessor metadata remains in its original immutable packet rather than copied evidence trees.
