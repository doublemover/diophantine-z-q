# The exact same-index scalar branch at 107 and its alternate marked lift

The translated index is retuned at the original fixed h, keeping
the old visible local rows and the cleared odd denominator. Its
explicit new odd depth at 107 rejects the two earlier named
admissions and the strict Γ receiver on this retune alone. There
is necessarily at least one further odd θ prime.

An alternate lift and a different opposite Selmer class have
a nontrivial crossed pairing whenever both are admitted. Their
joint admission is equivalent to a single explicit rational
norm equation in a fixed biquadratic field. A solution would
exclude the rational mark on this conductor-15 receiver. If
there is exactly one further θ prime, the admissions and the
two minimal Selmer dimensions are forced, giving rank zero.
Neither the support-count assumption nor a norm witness is
established. These statements do not concern the unchanged
scalar or exclude a different PointPair construction.

- [Exact 107 retune and the conditional scalar matrices](rc-native-helper-20261120/ct-original-constant15-nonnorm-retune-107-r1/EXACT-ACTUAL-NONNORM-RETUNE-AT-107.md)
- [Joint admission via one fixed norm](rc-native-helper-20261120/ct-original-constant15-alternate107-admission-norm-r1/EXACT-ALTERNATE-107-FIXED-NORM.md)
- [Alternate crossed sign](high-hom-1120/heegner-compressed-trace/constant15-retuned-107-alternate-lift-cross-r1/ACTUAL-RETUNED-107-ALTERNATE-LIFT-FISHER-SIGN.md)
- [Full-support crossed row](high-hom-1120/heegner-compressed-trace/constant15-retuned-107-alternate-full-support-row-r1/ALTERNATE-LIFT-FULL-SUPPORT-CROSSED-ROW.md)
- [Signed independent review](independent-review-nov20/constant15-same-h-107-retune-cross-admission-cold-r1/INDEPENDENT-SAME-H-107-RETUNE-CROSS-ADMISSION-REVIEW.md)

```sh
sha256sum -c SHA256SUMS
(cd rc-native-helper-20261120/ct-original-constant15-nonnorm-retune-107-r1 &&
 python3 -B replay_107_retune.py | cmp - EXACT-107-RETUNE-CONTROLS.json)
(cd rc-native-helper-20261120/ct-original-constant15-alternate107-admission-norm-r1 &&
 python3 -B replay_alternate_norm.py | cmp - EXACT-ALTERNATE-NORM-CONTROLS.json)
(cd high-hom-1120/heegner-compressed-trace/constant15-retuned-107-alternate-lift-cross-r1 &&
 python3 -B check_retuned_107_alternate_cross.py | cmp - EXACT-ALTERNATE-107-CROSS.json)
(cd high-hom-1120/heegner-compressed-trace/constant15-retuned-107-alternate-full-support-row-r1 &&
 python3 -B check_retuned_alternate_local_squareclasses.py | cmp - EXACT-ALTERNATE-LOCAL-SQUARECLASSES.json)
```
