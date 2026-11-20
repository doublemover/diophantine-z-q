# Independent check: alternate local criterion and known support

Independent mathematical/source review, 2026-11-20. Exact source notes bound here:

| Item | SHA-256 |
|---|---|
| NEXT-COVER-AND-ACTUAL-ODD-DISCRIMINANT-TEST.md | dfc383d97f13203f3e43d7cffb544b92347af2aaa0cb3b335feccdfd1ab3a178 |
| EXACT-SHARED-BRANCH-LOCAL-CLASSES.md | cf7fb20ca6295c6930e62fc1babffb216c389ae90d1fc863f8d2e21f8077d28a |
| EXACT-REMAINING-ODD-PLACES.md | e6778189ebdb1f447fc4b356383b8b36ccbffaf1274d67ce7574f8fd8bca3952 |
| ACTUAL-ALT-SUPPORT-AND-KNOWN-MATRIX.md | 84065756db6779a825e8a7c4f849e33784079136244657f5ee848334570a7fa7 |
| Support manifest SHA256SUMS | 218146ffeb0a68a14ee757ffb91b88b907050f54d0e19a67f187c252c413083d |

**Actual local criterion.** The two normalized conic parameter pairs map to the same alternate genus-one curve; the relative scale square gives degree two, with the two geometric lifts differing by a parameter-pair sign rather than an original ordinate sign. The determinant pencil has simple roots on the fixed data. A rational point lifts to a positive squarefree tau supported on the prescribed beta and H primes after the allowed normalization, not on L-prime.

At a new discriminant place, the nonshared branch fixes the class 1/7 of tau/Z and the shared branch fixes −1/7 by the two opposite unit tangent lines. These classes are the same when p is 1 modulo 4; in the other case exactly odd depth excludes the shared lift. At even depth the two scaled affine forms have distinct roots, their character sums give at least (p−5)/4 simultaneously nonzero squares for the eligible primes, and unit Hensel realizes the second class. At H primes the exact eigenline scalings 1±e and the canonical unit-line class 8 give both unit and both ramified classes. The depth-one reverse construction and the depth-at-least-two forward construction have different normalizations, both checked. At C primes the unit line proves the extra upper restriction when 3 beta is a square; other good and denominator primes have smooth genus-one reduction. The 2, 3, beta and real branches supply the stated small-place sufficiency. Direct finite character/eigenline tests and the prime-83 tangent replay passed; at 83 its exceptional shared row is x=14 with both ordinates zero. The Jacobi aggregate alone is redundant and does not solve the individual rows.

**Actual bounded scan.** Independently checked the fixed h and translated-index ratio equality, the chart-zero sign at O/T0 versus the two other 2-torsion points, and the literal use of its norm in Q. Both frozen Python controls reproduced byte for byte: ACTUAL-ALT-KNOWN-MATRIX.json b968f89b7a0716941a448fbe4c8a659f5fed5c2f91be8383a7e32eb2efac6324 and ALT-FORMAL-RATIO-CONTROLS.json d8b740ed7dcbe994e0467b7588c097cc38248f2b76f03b01375fedf0ab58437b. The latter distinguishes actual split O, actual split nontrivial torsion and actual inert O from its nonactual T0 canary. A pole gives an order-four residue of the indexed point. The Gaussian cyclic submodule argument then gives size at least 2^(2 v2(index)+3), and the Hasse lower bounds 32407 and 140737464628763. At inert primes the trace calculation gives 2-adic group-order valuation at most 5. This changes the lower bound for odd exceptional denominator factors but determines no denominator character.

Read exact calculator 588e265edc77a7e4f3f72a7ee846d8f041c714525a006be7a9b2ccd8ec1248fe and compiled it only in a scratch directory, with assertions enabled. Independently spot-replayed 10–10000 (only the known 83 hit), 2,000,001–2,100,000 (no hits), and dependent subset 20,000,001–20,010,000 (no hits). Reviewed but did not independently rerun the full supplied scans. The 20 million report covers the relevant symbol-(3 beta/p)=+1 locus after the specified fixed exclusions; the 20-to-120-million report covers only the extra dependent-symbol sublocus. They do not bound the other half of the larger interval.

**Finite matrix.** Independent elimination gives 11 pivots on 12 known columns and sole nonzero kernel mask 1643. Thus every right-hand side on the known 11 rows has exactly two realizations, regardless of the currently unknown actual reduced-denominator phases. A new row is dependent on these columns exactly when its kernel-product symbol is +1; this is a search criterion, not actual row inconsistency. New H columns, unseen L-prime/C support and individual reduced Z characters are still open. No adèlic class for the full system, rational point, global obstruction, or Lean proof is asserted.

Reviewed by the independent verification lane.
