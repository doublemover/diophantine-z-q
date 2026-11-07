# Independent reciprocal open-j review

Accepted. Fresh copied strict-kernel replay checks all 54 declarations in three modules. Source copies are byte-identical to the frozen producer; recursive audit permits only propext, Classical.choice, and Quot.sound.

The literal ordinary base is Z[j,1/(6N*j*(j-1728))]; the reciprocal base is Z[s,1/(6N*s*(1-1728s))]. The proof constructs actual localization lifts in both directions, proves the required denominator units, and verifies both inverse laws by localization and polynomial extensionality. The coordinate inversion direction is j -> s^-1 and s -> j^-1. Unit-based inversion remains meaningful even when N=0 degenerates the base; nonzero N is explicitly required where the denominator must be nonzero for the normal model.

The actual reciprocal cover map is the original algebra map composed with the proved inverse ring isomorphism. Its finiteness and etaleness are derived, not assumed anew. The polynomial scalar action for the second integral closure is the reciprocal coordinate, and the scalar tower is checked explicitly. Domain, finite original cover, etale original cover, and N != 0 remain visible hypotheses of finite_normal_model.

The actual Scheme factorization uses the already constructed projective chart at infinity and proves equality of the polynomial maps on constants and the generator. The resulting finite-type/quasi-finite claims concern exactly that map. It does not infer that the original open cover is proper or that the global normalization is finite before the section-ring transport.

Remaining geometric scope is accurately stated: actual global normalization chart transport, specified modular source/component, and regular/semistable/arithmetic/PEL identification. No mismatch found. No producer source was edited.
