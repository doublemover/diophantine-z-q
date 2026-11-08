# Rank-one modules on genuine target neighborhoods

This packet proves that a finitely presented flat rank-one module over a finite algebra is trivial on an entire inverse-image principal neighborhood of each point of the base. The basis is an actual `Fin 1` basis of the original localized module, not a dimension count or a localization at one selected source point.

`FiniteLocalRankOne318` proves the entire finite algebra over a local base is semilocal, then constructs a rank-one basis using the stated finite/flat/stalk-rank hypotheses. `RankOneTargetNeighborhood318.exists_basis` descends this basis to a principal open defined by an element of the original base ring. `FifthRankOneModuleNeighborhood318.exists_basis` specializes the statement to the original section-algebra map of the actual fifth completed quotient on either whole target chart. Its `original_preimage` identifies the actual inverse-image basic open.

The module hypotheses are explicit: finite presentation, flatness, and rank one at every source prime. This packet does not supply those hypotheses for an arbitrary source line sheaf, does not identify a localized module with an arbitrary restricted line sheaf, and does not construct a cover-independent Picard norm. The affine quasicoherent sheaf/module comparison available in pinned Mathlib is distinct from these remaining hypotheses and applications.

All three sources passed strict Lean checks with kernel typechecking retained. The target-only recursive audit covers all 11 imported declarations, including private declarations, with only propext, Classical.choice, and Quot.sound. The retained check3 log passes the semilocal source before an include-binder error in the next source; check4 fixes and passes that next source. The final actual fifth consumer passes its separate log. No predecessor or full-chain replay was performed. Hosted integration and non-author review are separate.

The optional uncompiled PicardGroup-dependent drafts are not part of this packet. No official Mathlib source was changed.
