# The raw Heegner trace is a rational double on each selected detector arm

For the exact balanced detector twists, the original oriented level-48 trace descends to twice a rational point. The ramified-prime argument uses places other than 17 and two literal support rows to identify the zero Kummer class inside the known eight-element Selmer group.

This identity does not give a nonzero trace or an actual marked point. If exact nonzero characteristic-zero coordinates are independently available, rational two-division with the stated torsion correction can recover the mark. The finite order-three test alone does not supply those coordinates.

- [Exact proof](proof/ACTUAL-LEVEL48-RAMIFIED-GENUS-AND-RATIONAL-DOUBLE.md)
- [Independent audit](independent-review/INDEPENDENT-LEVEL48-RAMIFIED-RATIONAL-DOUBLE-REVIEW.md)

Replay:

    cd proof
    sha256sum -c SHA256SUMS
    python3 -B replay_ramified_kummer_saturation.py | cmp - EXACT-RAMIFIED-KUMMER-SATURATION.json
