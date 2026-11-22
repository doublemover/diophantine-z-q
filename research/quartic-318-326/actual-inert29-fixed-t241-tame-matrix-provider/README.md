# The fixed 241-isogeny transfer on ordered level-48 flags

This package gives 726 actual isogenies on the three fixed supersingular source models at 29. Each arc records its exact (E[16]) and (E[3]) frame matrices, so an actual supplied CM embedding is weighted by its local determinant in one coherent orientation. All 48 independently computed split-reference histograms are recovered exactly. The separate nonsplit field control verifies nonzero local responses on the three models.

No complete selected moving discriminant is supplied, no moving CM multiplicities are computed, and no original rank or primitive phase is asserted. The earlier fixed (D=-1751), conductor-241 files are replay inputs and are not a transfer theorem.

```sh
sha256sum -c SHA256SUMS
cd proof/ct-level48-inert29-fixed-T241-tame-matrices-r1
OPENBLAS_NUM_THREADS=1 python3 replay_inert29_fixed_T241.py | cmp - EXACT-INERT29-FIXED-T241-MATRICES.json
python3 check_T241_inert_orientation.py | cmp - EXACT-T241-INERT-ORIENTATION.json
```
