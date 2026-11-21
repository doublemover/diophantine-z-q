# Exact norm-one recovery from an oriented Heegner ideal

The 2- and 3-adic parts of the marked CM ideal can be discarded without knowing the class number or a normalizing unit. Given the exact oriented ideal at the remaining primes, a degree-eight lattice has known minimum squared length eight and only two shortest elements. They are the two signs of its norm-one generator, whose relative residue sign is the mark test. This does not produce the required good-prime intersection ideal or evaluate an original trace.

- [Proof and finite Gram/eta replay](proof/ACTUAL-CM192-ORIENTED-IDEAL-SHORTEST-VECTOR.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-ORIENTED-IDEAL-LATTICE-REVIEW.md)

    (cd proof && python3 -B replay_oriented_ideal_local_and_gram.py | cmp - EXACT-ORIENTED-IDEAL-LOCAL-AND-GRAM.json)
    sha256sum -c SHA256SUMS
