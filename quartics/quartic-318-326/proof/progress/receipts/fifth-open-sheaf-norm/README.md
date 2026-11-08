# Actual all-open fifth norm and genuine unit-sheaf morphism

The norm is now defined on every actual target open. Nonempty opens use the proved regular section with the original generic field norm; the empty open uses its unique section. Multiplicativity, restriction compatibility, equality with both original complete chart norms, and pullback followed by eighth power are proved.

Invertible regular functions are constructed as genuine sheaves of commutative groups: coefficients and their inverses are glued in the original structure sheaf, and both inverse equations and uniqueness are checked. The norm is an actual morphism between these sheaves. FifthSheafNorm318.pullback is the original Scheme structure-map pullback on units, and pullback_norm proves its composite with the actual norm equals the eighth-power sheaf endomorphism. The norm components retain the exact previously proved field/chart values.

Five sources passed bounded strict kernel checks. A fresh target-only recursive audit passed 55 declarations, allowing only propext, Classical.choice and Quot.sound. The OpenDominantNorm check excerpt is explicitly labelled and bound to its original log; the later initial units-wrapper failure is not presented as a successful whole batch. Successful final unit, sheaf and identity checks are separately retained. Hosted integration and a distinct non-author review remain separate.

This constructs a norm of invertible regular functions, not a line-bundle or Picard norm. No identification of Picard groups with sheaf cohomology, no coverage of all source line-bundle trivializations, no source Jacobian, polarization or PEL realization is asserted. The pinned ring Picard API explicitly leaves its invertible-sheaf comparison separate.
