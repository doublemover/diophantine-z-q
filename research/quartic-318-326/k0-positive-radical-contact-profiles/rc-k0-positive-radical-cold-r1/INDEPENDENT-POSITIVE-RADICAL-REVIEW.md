# Independent cold review of the two-phase numerical Ready Sel4 family

**PASS for the exact paper and replay, 2026-11-21.** Author
`MANIFEST.json` SHA-256
`46e35e074151c8d0e00f37f0a298ee846c07c1e106ccdea88536ab185b9c36db`;
`STANDALONE-READY-FULL-MARKED-RADICAL.md`
`0d1290e923b0fa0ce082e9552d9cbdf35ba18b441b9d19d2b2028ad31eb9d5fe`;
author `SHA256SUMS`
`fe2e47365762c0cbbae7cc7141e39d11633bcdaacc7e2f5473265658842914ba`.
I checked the upstream hashes and replayed both phase controls to the
exact JSON SHA
`02c50a1f2baf0b8c788c6ca6b67538f7e47d6ef64d92a0884e9456f8d9f15744`
with the archived command. These controls do not replace the
uniform argument.

Independently, S and L are coprime odd integers whose difference is 2.
For every prime of 3β, their residues are respectively 1 and −1.
Thus D is coprime to A (including the entire square part of A), and the
actual reduced pole b has valuations (6,2,2) at (2,3,17) and one at each
of the six contacts. Its local square test at 2, 3 and 17 is exactly
the one for 17β; the phase-specific pairwise contact symbols are
unaffected. If z = D−288β, expanding A against z² gives
C−z² = 2304β(Δ−36β), strictly between 0 and 2z+1 for the stated
Δ threshold, so this is not the trivial square-C case. Positive b
tends to zero as j increases, hence gives infinitely many distinct
poles.

Put X = S²−2L², Y = 4KL. Direct expansion using S²−L² = 4Δ gives
X²+2Y² = D²+192βL² = B/3. X is odd; at any odd prime of K,
X = −1 modulo that prime, and at any odd prime of L, X = 4.
This proves primitivity and implies a nonzero residual root of −2
at every odd prime divisor of B/3 (at one of those primes Y cannot
also vanish). Every p≥5 factor in the already verified universal
first-coordinate pairing formula is therefore +1. D is an integer
square and every genuine first coordinate is a unit at its
denominator primes, so its Jacobi factor is +1 as well.
The conclusion uses the entire genuine Sel2, not the supported
subspace or specified-lift test. [Fisher, §1](https://doi.org/10.1007/s40993-022-00376-z)
then gives membership in the image of Sel4 with no Sha finiteness or
rank premise.

No rational k=0 point, fixed companion squareclass, literal folded
scalar, or original four-pole grid follows. No Lean or remote write
was used in this review.

Reviewed by the independent proof/CI lane.
