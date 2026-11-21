# The actual level-48 raw trace is a rational fourth multiple

For each selected balanced detector twist with the original \(n\equiv23\bmod24\) refinement, the raw oriented trace descends to \(4E_n(\mathbb Q)\). The proof identifies one coherent first-half sign at two ramified primes using a level-48 eta quotient, a degree-two cover, and a principal-ideal calculation. The first half is necessarily unmarked modulo rational 2-torsion. No trace nonvanishing, numeric pole, rank, or published formalization is claimed.

- [Proof and scope](proof/ACTUAL-LEVEL48-RAMIFIED-KUMMER-FOURTH.md)
- [Independent review](independent-review/INDEPENDENT-LEVEL48-RATIONAL-FOURTH-REVIEW.md)

Check the finite certificate and exact package with:

    (cd proof && python3 -B replay_level48_first_half.py | cmp - EXACT-LEVEL48-FIRST-HALF.json)
    sha256sum -c SHA256SUMS

The replay verifies all cusp-denominator orders, exact finite pair-sign identities, and local root-parity controls. It does not evaluate a CM class trace.
