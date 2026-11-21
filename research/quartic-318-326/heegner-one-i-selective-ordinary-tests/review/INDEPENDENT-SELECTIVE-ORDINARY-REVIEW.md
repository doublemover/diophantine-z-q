# Independent review: selective ordinary mirror readouts

**Verdict: passes the paper and finite replay review at the stated scope.**
This binds exact proof SHA-256
`fd460727e8e2f314979d5e479d0b183ac9e5cd5a601e26c6d5f03c886a375b09`
and author SHA-256 manifest
`d7fda2d61a18b29737bee721c5ef89638c5196eb2464dc2023fbbae3f15e2304`.
All three frozen author replays agree byte-for-byte with the bound
JSON. These are actual local calculations on the fixed one-I curve
and its degree-168 mirror field, not a global class group presentation.

- At a good prime ℓ≠13 a local cocycle value is represented by
  v modulo (g−1)V, for arithmetic Frobenius g. Restricting to the
  degree-f prime gives the value c((1+g+···+g^(f−1))v) for the literal
  mirror covector c. Changing the lift of v telescopes to
  c((g^f−1)w)=0. Passing to the additional common cyclotomic completion
  multiplies that value by its degree dividing 12, an invertible scalar;
  the same factor cancels on the ordinary character side. For a
  nontrivial unipotent g the length-13 readouts vanish and the fixed
  covector detects the local quotient. The distinct 1,a eigenvalue
  case has one independent fixed readout. At g=1 two independent fixed
  readouts suffice. The bad rational primes/13 use their already
  established zero strict local conditions. Thus detection of a
  supplied strict character can use only degree-one primes.
- A relative split prime with invertible g−1 needs degree at least
  three: a nonfixed covector and its translate in an orbit of length
  two would be independent and force g²=1. Without a 1-eigenvalue
  that means g=−1, whose projective orbit is already fixed. The
  checked point counts/matrix orbits show the least norm is 1951³ =
  7,426,288,351, with the stated squarefree degree-84 factor and
  nonzero signed root specifying one actual prime. This is only the
  least norm for good forced-zero tests of that particular type.
- The six actual degree-two primes above 5303 are tied to the fixed
  degree-one mark by their checked quadratic factors and signed Z
  residues. The old B,Z values recover the primitive-root phase 10;
  the superseded phase metadata 12 is not used. Frobenius exchanges
  the j,−j labels and the alternating Weil form gives c_j(Q)=c_0(Q)
  for all six. Therefore each degree-two strict-character readout
  is exactly twice the degree-one marked readout. These are relations
  in the strict test quotient, not individually principal ideals or
  asserted independent relations in the ordinary class group. The
  old composite principal row likewise becomes a smaller *strict test*
  only after imposing the actual q53 and q3 strict zeros.
- The class-generation bound uses the constant-four clause of
  [Grenié–Molteni, Corollary 3.7](https://arxiv.org/pdf/1607.02430),
  **assuming GRH**. The actual absolute log discriminant is below its
  degree-dependent threshold, and the rigorous atanh series determines
  floor(4 log²|D|)=147,866,716. A supplied nonzero strict character
  is detected at a good rational prime up to that cap by the local
  reduction. This is a conditional injectivity statement, not a rank
  upper bound or strict character enumeration.
- For the affine Euler quotient, nonidentity scalar Frobenius is
  conjugate into the scalar subgroup and gives the cyclic orbit list
  with one extra fixed label. Pure nonzero translation gives a single
  13-cycle in degree 13 and full splitting in degree 12. At ramified
  primes inertia meets translations trivially, by unramifiedness over
  the ordinary mirror. Inertia's unique affine fixed point is then
  preserved by decomposition, so the same fixed-label permutation
  comparison applies after taking inertia invariants. This verifies
  cancellation at the ramified primes and the displayed positive
  Euler ratio for the remaining translation primes.

No new projected class dimension, independent global class relation,
rational point, or formal Lean result is established here.

Reviewed and signed: **Vesper, independent mathematics review**,
2026-11-21 UTC.
