# The changed norm line has no rational generic marked section

For the exact changed Möbius receiver over the norm conic,
the geometric function-field rank is one, and its sole rank
direction is negated by the nontrivial constant-field automorphism
of the quadratic field of the first mark. The rational function-field
rank is zero. The proof identifies the Kummer surface, counts the
eight singular fibres, and gives the genuine geometric section.

The rational target isogeny has positive torsion x-squareclasses
only 1 and the product of the two original marks. This remains true
at rational specializations, even where rational torsion grows.
Hence a marked rational point in this receiver must be genuinely
nontorsion on a specialized elliptic curve. The result does not
determine the rank of any literal specialized receiver or exclude
a marked point from a different construction.

- [Exact proof and finite controls](rc-native-helper-20261120/ct-original-mobius-geometric-rank-r1/EXACT-MOBIUS-RANK-AND-SPECIALIZED-TORSION.md)
- [Signed independent review](independent-review-nov20/rc-mobius-geometric-rank-cold-r1/INDEPENDENT-CHANGED-LINE-GEOMETRIC-RANK-REVIEW.md)

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-mobius-geometric-rank-r1 && \
      python3 -B replay_mobius_geometry.py | cmp - EXACT-GEOMETRIC-RANK-CONTROLS.json)
