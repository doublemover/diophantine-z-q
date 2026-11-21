# Opposite Ready controls for the constant-15 receiver

Two explicit standalone rational Ready poles have the same even root sign,
the same two isogeny-Selmer dimensions, and matching local obstruction
types at 29. One has rank two and a marked PointPair; the other has
certified rank zero and no rational point on this particular constant-15
receiver. Neither pole is an output of the original linked source.
The negative result does not exclude an unrestricted PointPair.

- [Exact paper](high-hom-1120/heegner-compressed-trace/original-constant15-opposite-ready-controls-r1/CONSTANT-15-MARK-HAS-OPPOSITE-READY-CONTROLS.md)
- [Finite replay output](high-hom-1120/heegner-compressed-trace/original-constant15-opposite-ready-controls-r1/EXACT-CONSTANT15-OPPOSITE-READY-CONTROLS.json)
- [Signed independent review](review/INDEPENDENT-CONSTANT15-OPPOSITE-READY-CONTROLS-REVIEW.md)
- [Exact receiver and back-map derivation](rc-native-helper-20261120/ct-original-constant15-marked-receiver-r1/CONSTANT-15-MARK-AND-UNIFORM-29-SOURCE-GATE.md)

Run `sh verify.sh` from any directory. Runtime is about ten seconds.
Python 3, the standard library, `sha256sum`, and `cmp` are sufficient.
The receiver source is included for the mathematical dependency; the
controls do not read it at runtime. The author and reviewer digests
remain the exact reviewed bytes.
