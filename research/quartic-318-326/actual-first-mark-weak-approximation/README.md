# An actual first marked point and the remaining companion problem

For any fixed literal Ready pole and its already selected local seed,
one rational parameter constructs infinitely many *new* common twist
pairs with the old squareclasses at every prescribed finite place.
The first original mark \((\beta,1)\) is represented by a rational
nontorsion point. On its same \(\theta\)-companion the same mark is
everywhere locally admissible. The first construction does not
preserve the two exact Selmer sizes automatically.

For nontrivial \(\theta\), the **specific** parameter line used here
has no generically nontorsion companion section. This does not
exclude companion points at rational specializations or on a
different construction. This package gives no second marked point,
unconditional PointPair, full original solution, or Lean validation.

- [First-mark proof and exact companion limit](rc-native-helper-20261120/ct-original-first-mark-weak-approximation-r1/FIRST-MARK-WEAK-APPROXIMATION-AND-COMPANION-BOUNDARY.md)
- [Signed independent review](independent-review-nov20/rc-first-mark-weak-approximation-cold-r1/INDEPENDENT-FIRST-MARK-AND-COMPANION-REVIEW.md)

The two earlier notes and manifests are provenance, not new claims.
The Python replay verifies the exact finite arithmetic on the stated
toy data; it is not a literal original pole or a computation of
either analytic rank.

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-first-mark-weak-approximation-r1 && \
      python3 -B replay_first_mark.py | cmp - EXACT-FIRST-MARK-LOCAL-CONTROL.json)
