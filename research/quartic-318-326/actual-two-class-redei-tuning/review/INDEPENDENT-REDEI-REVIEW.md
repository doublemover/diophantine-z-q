# Independent review: two Rédei signs for the actual two-class cover

**Verdict: passes independent paper and finite-witness review.**
This binds the source note SHA-256
`dacabb15b66f5cda40cbd4fddb5b5cd17bc2535187d4ff6aa6f643c7aa4a2866`
and author manifest SHA-256
`415469f3f3cf13c0ab1c038f7e7a76a4378f90bda38d9804f6ef0e417e6a5648`.
I verified the manifest and replayed the independent-squareclass witness
from the original archived scales: modulo 4818481 the two scaled roots
are 43482 and 2576363, so their difference is 2532881, a nonsquare, while
2399 is a square. This distinguishes the two positive rational classes
over Q and over Q(i). No numeric moving prime is used by the witness.

- **Primitive Artin calculation.** Clearing the affine norm coordinates
  in either conic changes their least positive denominator by a rational
  factor supported on the fixed B-primes, which contributes Jacobi sign
  +1 by the B-local squares and the support primes being 1 mod 8. At an
  odd prime outside the two norm radicands, a split pair of conjugate
  factors cannot both be divisible, by primitivity; the surviving
  valuation is even. At an inert prime no divisibility is possible.
  Thus arbitrary primitive and minimally ramified Rédei generators differ,
  up to the relevant squareclasses, by a rational twist supported on the
  radicands and 2, with possible sign. This follows by dividing their
  ratio by a rational square root of its norm and applying quadratic
  Hilbert 90. At the λ test primes the affine norm coordinate
  W₁ + √b V₁ has the original marked character γₐ, independently of the
  root signs, since its conjugate product is the square unit t. At the
  κ test primes p dividing b, the formal Rédei base Q(√(bδ₀)) has the
  same local completion as Q(√D), with residue degree one, since
  aδ₀ is a square unit. The norm generator reduces to the cleared
  denominator times a square root of aδ₀. A rational twist at a factor
  r of b has local squareclass D/r at r because D is a square in that
  completion; its character there cancels the other b-prime factors
  by quadratic reciprocity, using (a/r)=+1. All dyadic and sign twists
  have trivial character at the odd test primes. These checks retain the
  primitive denominators and give the claimed formulas after reciprocity.
  The expanded triples satisfy all pairwise local Hilbert conditions
  and the three-discriminant gcd condition, also for the repeated slots.
  See [Stevenhagen, Definitions 7.1, 7.6, 7.8, Lemma 7.7, Theorem 7.9
  and §8](https://arxiv.org/pdf/1806.06250).
- **Simultaneous signs on the exact old ray.** Over Q(i) the two D₄
  extensions intersect in Q(i,√a): a proper nontrivial D₄ quotient is
  abelian, and their biquadratic subfields share only √a. At a prime
  dividing a, the inertia of their composite acts nontrivially on √a
  and trivially on the other two quadratic generators. Commuting this
  inertia element with an element flipping only √2399 in the first
  component gives its nontrivial center, trivial in the second.
  Commuting with a flip of only √δ₀ in the second produces the other
  center. Both commutators restrict trivially to the intersection with
  the exact old order-clone and reciprocal-ray composite, because the
  clone is unramified there and the S′-ray is abelian. The intersection
  therefore lies in the joint three-quadratic subfield. The exact
  retained base Frobenius fixes its three generators by the B-norm and
  reciprocal p|a constraints. Both center bits can consequently be
  prescribed while that same base Frobenius representative is retained.
  The fourth-power norm refinement at p|a keeps the old square bit and
  still leaves split coordinates outside μ₄. The enlarged finite field
  adds no rational ramification to the old sieve exception set, so the
  reviewed late Gaussian rays remain disjoint and the same two-tail
  argument applies. Chebotarev here supplies existence, not a numerical
  prime.

The resulting choices make both tested Cassels signs +1, giving
orthogonality to the verified three-dimensional pair-supported
subspace W on the actual family. This is not full 2-Selmer
orthogonality, a Sel₄ lift, a rational point, a zero Sha class, or a
formal Lean result.

Reviewed and signed: **Vesper, independent mathematics review**,
2026-11-21 UTC.
