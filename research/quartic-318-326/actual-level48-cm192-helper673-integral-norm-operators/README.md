# Exact degree-12049 and five other framed reference operators at 673

This reproduces a saturated maximal quaternion order on the named j=209 model and all exact numerical framed Hecke rows at the six reference primes 13, 17, 31, 97, 337, and 12049. The computation uses integral rank-four Hom lattices. Exact row multisets with their common level sign match the separate direct Vélu computations at 13, 17, and 337. The package includes the signed independent replay and all mandatory inputs. It does not contain the evaluation on the selected reference word, an original global numerical twist, a point, or a rank assertion.

The directory named `quaternion-seed-r1` preserves the immutable downstream replay path; its proof is the corrected r2 and its machine files are byte-identical between those versions.

To reproduce the complete exact 23,596,272-byte JSON without storing it in this packet:

```sh
export PYTHONDONTWRITEBYTECODE=1
export REPLAY_JOBS=6
python3 ct-level48-cm192-helper673-quaternion-seed-r1/replay_helper673_quaternion_seed.py | cmp - ct-level48-cm192-helper673-quaternion-seed-r1/EXACT-HELPER673-QUATERNION-SEED.json
python3 ct-level48-cm192-helper673-norm-lattice-r1/replay_helper673_norm_lattice.py 13,17,31,97,337,12049 > /tmp/EXACT-HELPER673-SIX-REFERENCE-OPERATORS.json
sha256sum /tmp/EXACT-HELPER673-SIX-REFERENCE-OPERATORS.json
```

The expected SHA-256 of that exact generated JSON is `445ff25984ab5f6d34a8f92f4e8fea37a7ff3e44ea538c35930c3b8f0e543afc`. A serial run selects one worker by setting `REPLAY_JOBS=1`.
