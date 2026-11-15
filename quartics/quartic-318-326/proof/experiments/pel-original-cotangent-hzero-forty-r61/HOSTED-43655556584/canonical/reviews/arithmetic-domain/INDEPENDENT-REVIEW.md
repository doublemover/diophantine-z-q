# Independent original arithmetic-domain repair source review

Source-only verdict: PASS for future hosted checking, not a compilation claim.

Candidate geometry-20261115/repairs-43655556584/IntegralSourceArithmeticDomain318.lean SHA256 794610bd4e93f0819469b2be3109452395f02ff6fb0b783b1f8cb1e86f647c04. Before source matches published center71 at 6b664f8406d512c50432425e3bd616447ff8ad8e. Read the entire candidate, exact two-body diff, current center71 actual failure, actual integral contacts definition, and pinned Polynomial Eval/Coeff declaration.

The four literal contacts are unchanged:0,32,76832,-343. Separate Fin4 cases invoke actual ring-hom preservation of zero/natural casts/negation, rather than relying on norm_num to remove arbitrary algebraMap casts. The negative case retains its sign and proves the negative natural-cast equation by map_neg followed by congrArg negation. This directly targets the three authentic residual numeric goals.

Pinned Polynomial.map_injective has explicit ring-hom parameter f followed by injectivity hf. Passing (algebraMap R ℚ) before hR corrects the authentic mismatch where hR was supplied in the ring-hom position. The polynomial algebra is still the actual mapRingHom algebra; no alternate coefficient map is introduced.

All4 monic presentations, rational twists, full tensor base-change equivalence, actual includeRight map, whole-order injection, and resulting domain structure are unchanged. The original injectivity premise hR remains; fraction-ring inputs still produce it. No new domain/component premise, lost root, weakened statement, public binder change, resource option, or trust escape appears. Actual center71 passed the preceding IntegralOriginalGlobalPair module and then failed this module in4.123s. This report does not claim parameter2 evidence or blanket active-copy propagation: each intended successor still needs its own current contract, immediate predecessor, and exact-copy evidence. No local Lean was run.
