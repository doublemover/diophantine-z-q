# A fixed 48-class base for the literal fixed-103 first arm

The original fixed-final-prime selector gives the potential first twist (n=1751c) on the same literal detector: it does not pick a new pole or replace the original source. The exact computation here is the entire indexed and oriented maximal-order base for discriminant (-1751) at the good inert prime 29. The paper spells out the genus-character signs on the relative conductor kernels and the sufficient odd-order readout. It gives neither the actual conductor (c) nor its primitive weighted aggregate.

The prior oriented-coordinate ladder is included only at the two exact, pinned byte inputs needed for a standalone replay. The numerical and arithmetic claims concern the new 48 indexed rows, including reduction multiplicities. The separate raw (c=1) calibration and any positive conductor experiment are not part of this package.

```sh
sha256sum -c SHA256SUMS
cd ct-level48-fixed103-D1751-inert29-base-r2
REPLAY_JOBS=5 python3 replay_fixed103_D1751_base29.py | cmp - EXACT-FIXED103-D1751-BASE29.json
```
