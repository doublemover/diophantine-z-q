# Independent review: the full conductor-one CM −15 jet at 5

Signed: Vesper, independent cold reviewer. 2026-11-21 UTC.

Exact author manifest:
`1b2ade9e1ed33302ffdf7a6787df459f54cefb3d9898e43a1d5c45a71b49c660`.
All three author byte hashes and standard-library JSON replay checked.

- Verified the two singular j-values and Hilbert field against
  [Kumar–Kuwata, Example 9.3](https://www.cambridge.org/core/journals/nagoya-mathematical-journal/article/elliptic-k3-surfaces-associated-with-the-product-of-two-elliptic-curves-mordellweil-lattices-and-their-fields-of-definition/A5C4A0F2BA2DD613BBA2A5B83181DB86).
  The two horizontal edges select one prime over 2 at each stage;
  the repeated directed sequence is nonbacktracking. The two signs
  describe the two level orientations, not four classes in one sum.
- In [Maier, Tables 2, 4 and equation (1.6)](https://arxiv.org/pdf/math/0611041)
  the reciprocal ratios have leading q⁻¹. Their exact Laurent identities
  recover the ordered degeneracy maps. In particular, the second
  map at n=4 is C(C+8). There is only a double pole at infinity for
  the final T₁₆(2z), by degree and the local q² map.
  [Tian, Proposition 2.1](https://arxiv.org/pdf/1210.8231) gives the
  elliptic model, cusp at 0, and precise eight cusps. The two
  nonreal T₁₆ cusp values and Tian's nonreal x-coordinates fix the
  linear slope at +1: the exact x-coordinate is T₁₆(2z)+2.
- The two class labels use a common ordinate sign: the nontrivial
  Hilbert automorphism negates ε and ρ, fixes ερ, and transports the
  marked point. It is the relative unramified Frobenius over
  Q₅(√−15), not the automorphism over Q₅(ε). The displayed ordinate
  convention gives (1,ε) for the signed difference on X₀(32).
  The degree-two quotient followed by its rational scale gives
  (5/4,−3ε/8) and invariant differential factor 2.
- The independent polynomial-quotient checking script here derives
  both exact signed differences, differentiates the two modular
  coordinates using the displayed invariant differential, and
  independently doubles the rational twist point twice. The
  result has good smooth cusp reduction (1,1) and parameter
  −x/y=4; the signed invariant-differential computation gives
  the same 4. Reversing the one common ordinate sign reverses
  the result but cannot change whether it is nonzero.
- The explicit first-order two normalized Vélu quotients select
  the correct sign of the prime-square generator: their correct
  final coefficient is s=(1−ερ)/2. The first coefficient in
  [1]−[2]Ω is therefore 1+2ρ, and the independent reduced coefficient
  check gives the same. Multiplying by ρ/(−3) gives 2(1−ρ),
  agreeing with the Hasse coefficient of the lifted short family.

This is a full finite comparison on a genuine two-class oriented
CM orbit at level 32, not just a local CM automorphism test. It does
not evaluate a marked weight of the unrelated large-level target
form, a production mover jet, the required fixed-place higher lift,
or a PointPair.

Independent auxiliary replay requires SymPy:
`python3 -B check_independent_cm15_jet.py | cmp - INDEPENDENT-EXACT-REPLAY.txt`.
The bound author's own replay uses only Python standard library.
