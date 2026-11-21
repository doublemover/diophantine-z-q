# Independent review: a forced supersingular zero at every actual mover

I checked the exact production critical divisor paper (author manifest
`de50365e96655d814ca41a7c8551440044590e00346a4f822ef7228a2b25660d`,
paper `67e33759ba50e92b2b148d33adc7c3ac4a70e08632938c0b75b370eb1215643e`).
The author replay matched byte-for-byte. The independent replay here derives
the bad signs from the literal curve, enumerates integer divisors independently,
and uses binary Jacobi reciprocity rather than the author's Euler powers.
It agrees on all 127 nonidentity rows, 21 fixed-locus rows, 13 positive
eigenvalue rows, and four inert types in both mover phases.

* The modular argument is on the marked curve. If a characteristic-zero
  point is fixed by the degree-d Atkin involution, the actual quotient
  endomorphism sends E[d] onto the same cyclic mark C_d and takes the
  complementary level mark to itself. Its square kills E[d], so factors
  through [d] with residual degree one. That automorphism preserves the
  complementary cyclic mark since d is prime to its order, and preserves
  C_d since it commutes with the endomorphism in the commutative
  characteristic-zero endomorphism algebra. The full 2/3 marks exclude
  the extra cubic/quartic automorphisms. The sign must be negative because
  a nonsquare positive d has no square root in an imaginary quadratic
  field. Conversely the squarefree norm-d kernel on the complex curve
  with order Z[sqrt(-d)] is cyclic, and the characteristic polynomial
  X²+d supplies stable complementary lines exactly at the indicated
  odd-prime residues (at 2 the repeated root always gives a stable line).
* For d=770 the actual odd complementary roots are 1 modulo 3, 9 modulo
  37, and 1066 modulo 2399. The lower curve's a_p are
  (+,-,-,+,-,+,-) in prime order 2,3,5,7,11,37,2399; the exact squarefree
  Atkin product w770 on its differential is +1. The two pilot phases
  are (+,-,+,-,+,+,+) and (+,+,+,-,+,-,+), with p=1 mod 8 in both.
  Reciprocity gives (-770/p)=-1 in either phase, including 415721 itself.
  The historical marked producer (manifest `70410179d9e116b8c39b8f19c8afc2a4434d267caf6b863fd37cf0841c0d565e`)
  imposes the individual a and b phases. Its second b variation replaces
  the order/ray constraints at 11 and 2399, not the rational norm
  squareclasses there. The parallel all-fresh source (manifest
  `9633f407794cd248c916b78a6a7ec7688c190bbdb11126670fae5bc4fbfa665b`)
  explicitly retains the same individual a-type and b-type phases;
  neither argument infers them from the product being a local square.
* Every actual mover is prime to 2N. Passing over a finite local
  extension of good reduction for the CM elliptic curve and extending
  its prime-to-p marks gives a noncuspidal point of the same tame model.
  The two distinct cusp labels for infinity and its Atkin image stay
  disjoint, so the specialized involution is nonidentity. Its derivative
  at the fixed point is -1 in odd characteristic; formally its first
  nontrivial higher coefficient could not survive squaring if the
  derivative were +1. Therefore the eigenvalue +1 differential
  vanishes at that fixed point, which is supersingular by inert CM
  reduction. This proof includes the historical mover, rather than
  excluding an unspecified finite set. It forces some supersingular
  zero at each mover; it does not force a specified anchor to be a zero,
  prove absence of a positive sparse certificate, or count distinct
  specializations for the four fields.
* The separate non-CM argument is valid just as a finite-cap refinement.
  [Lombardo, Theorem 1.1](https://arxiv.org/pdf/1501.04600) over the fixed
  compositum gives independent SL2 factors for distinct geometric
  non-CM isogeny classes; choosing all isogeny identifications is
  unambiguous projectively at sufficiently large auxiliary prime.
  One tweak per permutation cycle puts the product in a split diagonal
  class of maximal order in its prescribed square or nonsquare
  determinant coset. Taking the full return reduces that order by at
  most the finite order of the lift on the defining compositum.
  Supersingularity allows a Frobenius eigenratio only of order at most
  six (a degree-at-most-two root of unity by slopes and Weil), and
  semisimplicity makes the corresponding power of Frobenius literally
  scalar, so no unipotent exception appears upon reduction modulo the
  auxiliary prime. This does not assert that the old infinite Gaussian
  gcd-tail proof transfers unchanged after adding the cap.

Replay from the workspace root, with the author's JSON as argument:

```
python3 -B check_independent_forced_marked_zero.py /path/to/EXACT-ACTUAL-FORCED-CRITICAL.json | cmp - INDEPENDENT-BAD-NODE-AND-ATKIN-REPLAY.json
sha256sum -c SHA256SUMS
```

Signed: independent reviewer, 2026-11-21 UTC.
