# A class-character obstruction for the selected level-48 mark

For the actual balanced twists the marked relative ideal is a nontrivial order-two class invisible to quadratic class characters. The companion norm-conic test gives a concrete characterization of which quadratic characters could lift to a separating quartic character. On the first selected arm \(u=1\), without a repair prime and with \(q_0\equiv7\bmod24\), the exact Selmer matrix forces that characterization to fail: the marked class belongs to \(4\,\mathrm{Cl}(L)\). The same fourth-power result is not asserted for all companion supports.

This does not evaluate the signed Heegner intersection ideal, its sign, the actual twist's rank, or an octic character.

- [Quadratic genus obstruction and fixed real quartic](quadratic-genus/ACTUAL-CM192-QUADRATIC-GENUS-OBSTRUCTION.md)
- [Finite norm-conic and quartic character test](finite-conic-test/ACTUAL-CM192-QUARTIC-CHARACTER-FINITE-TEST.md)
- [Exact first-arm order-four obstruction](first-arm-no-quartic/ACTUAL-CM192-NO-QUARTIC-DETECTOR-ON-BASE-ARM.md)
- [Signed independent review](independent-review/INDEPENDENT-CM192-QUADRATIC-AND-QUARTIC-BLINDNESS-REVIEW.md)

    (cd quadratic-genus && python3 -B replay_cm192_fixed_real_quartic.py | cmp - EXACT-CM192-FIXED-REAL-QUARTIC.json)
    (cd first-arm-no-quartic && python3 -B replay_base_sharp_kernel.py | cmp - EXACT-BASE-SHARP-NORM-KERNEL.json)
    sha256sum -c SHA256SUMS
