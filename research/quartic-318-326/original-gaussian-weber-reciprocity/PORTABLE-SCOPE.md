# Gaussian Weber Artin realization for the original linear-q route

This self-contained mathematical source packet constructs the actual
Gaussian field and its correctly oriented arithmetic Frobenius for the
same signed tag, without invoking either global class field theory or a
prime theorem in Gaussian progressions. The algebraic rank-one basis
in §1 replaces the uniformization route in the immutable r1.

* **Main proof:** EXACT-GAUSSIAN-WEBER-RECIPROCITY.md.
* **Finite appendix:** EXACT-GAUSSIAN-WIDE-NORM-KERNEL.md proves the
  exact commutator and wide norm; the main proof independently supplies
  the actual cyclotomic inclusion with the Weil pairing, so the old CFT
  inclusion route in the appendix is not a premise.
* **Independent scope:** the review binds the exact r2 proof hash.
* **Reproducible bounded controls:** `python3 local_control.py` and
  `python3 factor_control.py`, compared with the supplied output files.
  These verify small point-action and factorization calculations, not
  the field theorem or a large production prime tuple.

This is a paper result with cited standard elliptic-curve theorems.
It is not Lean admission, proof-map acceptance, or a CI marker.
Frei–Tinková Theorem 1.4 and the audited ordinary exclusion estimates
remain separate analytic ingredients. No pair of rational elliptic
points, restricted rank result, or final quartic solution follows
from publishing this packet.
