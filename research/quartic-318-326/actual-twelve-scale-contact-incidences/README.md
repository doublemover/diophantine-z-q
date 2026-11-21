# Twelve local incidences and why at least twenty-four are needed on this branch

For the same original scalar index J and four literal labels, the [exact twelve-contact certificate](linked-detector-twelve-compatible-incidences-r1/ACTUAL-TWELVE-COMPATIBLE-INCIDENCES.md) gives one real-checked index h and one common rational square t. At each designated prime the corresponding unchanged stored detector coefficient has valuation +1 and the other rows' contact factors are units.

| Literal slot | Four designated primes (all at the root −1) |
| --- | --- |
| 190 | 3162001, 52056721, 17590513, 1476960817 |
| 241 | 3641809, 53279089, 4818481, 344853841 |
| 292 | 4247281, 95810641, 16688017, 583021393 |

It retains every congruence of the [previous six-contact certificate](linked-detector-six-compatible-incidences-r1/ACTUAL-THREE-COMPANION-PRIMES-PRESERVE-THE-TRIAD.md), not the numerical h or its exact scalar output. Each nominated four-prime product passes the saturation character test at every prime through 47, but the next failures at **59, 59, and 53** require another prime in each of these three distinct classes.

The separate [cross-symbol proof](linked-detector-cross-symbol-support-r1/ACTUAL-SATURATED-CROSS-SYMBOL-SUPPORT.md) shows that all nine other nonzero root classes have nonempty odd support, already witnessed by a unit nonsquare at a retained [triad](linked-detector-three-scale-incidence-r1/ACTUAL-THREE-SCALE-THREE-PRIME-INCIDENCE.md) prime. The [exact collision router](linked-detector-three-scale-prime-router-r1/ACTUAL-THREE-SCALE-ODD-CONTACT-ROUTER.md) makes those supports disjoint. On the specified saturated square branch, with d=B^N, r primitive at B, and sufficiently large real t, a completion preserving respectively the triad, six, or twelve therefore needs at least **15, 18, or 24** distinct odd-support primes. The 36 bound after twelve is only under the stronger assumption that every support prime stays in the old 7-nonsquare Gaussian ray. Exact diagonal and off-diagonal signs constrain any proposed completion; neither the lower bounds nor the named primes give a complete support.

[Independent review and two replays](joined-twelve-cross-symbol-cold-r1/INDEPENDENT-REVIEW.md) use separate lifted group/real arithmetic and exact rational symbol arithmetic. Run `sh replay.sh` offline with Python 3, `sha256sum`, and `cmp` (the original 32768-bit author real control is the slowest step). No discovery scan is required. The small d=204 is a modular replay only. This is not a square pole denominator or rational PointPair construction, and is not Lean-verified.
