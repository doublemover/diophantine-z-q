# An exact order-nine primitive reference at the fixed conductor 241

All 11,520 oriented ring-class terms of discriminant (-1751cdot241^2) are evaluated in characteristic 29. The exact primitive quadratic-genus phase is (4) modulo (9), up to a common sign. It proves a nontorsion component on the reference rational twist (E_{421991}) using reduction at 29 and split Tate torsion at 3, without an analytic or 2-converse implication.

This is deliberately a **fixed reference**. It does not evaluate the primitive character for any complete, selected original detector conductor. An extension of the reference character to a larger ring class field would be imprimitive; this replay is not evidence that its value transfers to a different primitive character or that it produces the original marks.

Unchanged base and oriented-coordinate Python inputs are included so the replay is self-contained. The corrected fixed base proof is a separately reviewed package.

```sh
sha256sum -c SHA256SUMS
cd ct-level48-fixed103-D1751-conductor241-pilot-r1
OPENBLAS_NUM_THREADS=1 REPLAY_JOBS=7 python3 check_fixed103_conductor241.py | cmp - EXACT-FIXED103-CONDUCTOR241.json
```
