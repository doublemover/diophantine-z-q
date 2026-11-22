# Complete level-48 primitive control: D = −311, conductor 241

The reviewed example enumerates all 19 characteristic-zero base classes and every one of their 242 inert conductor-241 lines. The absolute named Weil/Gauss convention gives integer signed phase 101, hence exact order nine. The same orientation gives the real CM product powers R^560 = γ² and R^280 = γ at the specified 29-place.

This is a bounded numerical control, **not** a chosen original detector and not a computation of its complete oriented intersection ideal. The separate signed subtotal above 11 is not included or inferred. The fixed matrix and auxiliary scripts under `proof` are the exact reproducibility donors, not new results in this packet.

```sh
sha256sum -c SHA256SUMS
(cd cold && sha256sum -c SHA256SUMS)
(cd proof/ct-level48-D311-fixed241-direct-control-r2 && sha256sum -c SHA256SUMS && OPENBLAS_NUM_THREADS=1 python3 -B check_D311_fixed241_direct.py | cmp - EXACT-D311-DIRECT-CUBIC.json)
```
