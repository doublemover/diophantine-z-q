# The three literal detector first witnesses on the common four-pole source

The independently reviewed [paper](author/THREE-ORIGINAL-READY-DETECTORS-T18-NATIVE-ROWS.md) fills the first-witness equations at the original detector slots 190, 241, and 292 using normalized `t=18`. When the existing preparation supplies one common index, those three points coexist with the separate scalar first witness at that same index. Each remaining detector row block is equivalent to one explicit affine rational-point test on its actual companion. No key, companion point, rank, or solution of the four-pole system is produced.

The [signed independent review](cold/INDEPENDENT-THREE-DETECTOR-ROWS-AND-FOUR-FIRST-REVIEW.md) includes a standard-library replay of all 15 native row formulas. The two unchanged source specimens in `input/` are named `.lean.txt` for replay only; they are not imports or a new Lean build claim.

```sh
sha256sum -c SHA256SUMS
(cd author && sha256sum -c SHA256SUMS)
(cd cold && sha256sum -c SHA256SUMS)
python3 -B cold/replay_native_three_detector_rows.py \
  input/Raw318FinalReplayData.lean.txt input/ThreePoleCertificates318.lean.txt |
  cmp - cold/EXACT-THREE-DETECTOR-RAW-ROWS.txt
```
