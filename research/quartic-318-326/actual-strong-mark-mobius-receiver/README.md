# A changed norm line for the exact original companion mark

Fix the already prepared literal Ready pole, its two squareclasses,
and its selected local seed. The construction does not alter that pole
or the two classes. It chooses an auxiliary rational point on their norm
conic and proves everywhere-local solubility for a single explicit
genus-one quartic that would give both marks on one common twist pair.
The line can preserve any specified finite old local squareclass
conditions.

The exact Jacobian identifies the remaining arithmetic question:
whether one positive squareclass is in its true rational isogeny
Kummer image. A rational point must also lie on the required open.
Local solubility does not provide that point, either Selmer size eight,
or an unconditional original PointPair. The finite replay's positive
numerical example is an arithmetic control, not an original pole.

- [Proof, exact receiver and finite control](rc-native-helper-20261120/ct-original-strong-mark-mobius-receiver-r1/CHANGED-NORM-LINE-AND-EXACT-MARK-RECEIVER.md)
- [Signed independent review](independent-review-nov20/rc-strong-mark-mobius-receiver-cold-r1/INDEPENDENT-CHANGED-LINE-EXACT-MARK-REVIEW.md)

This is a paper-only package; no Lean validation or rank computation.

    sha256sum -c SHA256SUMS
    (cd rc-native-helper-20261120/ct-original-strong-mark-mobius-receiver-r1 && \
      python3 -B replay_changed_line.py | cmp - EXACT-STRONG-MARK-RECEIVER-CONTROL.json)
