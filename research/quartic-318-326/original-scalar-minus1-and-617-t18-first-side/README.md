# Exact first-point transfer for original inputs −1 and 617

This supplies only the first native PointPair equation on the two retained actual scalars. Input −1 reuses the exact fixed input-zero point, with its own scalar scale. Input 617 specializes the same identity to its own different fixed curve and marked point. Neither companion, the complement, a rank, or a simultaneous four-pole witness is computed here.

- [Exact proof and source bindings](author/ORIGINAL-SCALAR-MINUS1-AND-617-T18-FIRST-SIDE.md)
- [Independent signed review](cold/INDEPENDENT-SCALAR-MINUS1-617-T18-FIRST-SIDE-REVIEW.md)

```sh
sha256sum -c SHA256SUMS
(cd author && sha256sum -c SHA256SUMS && python3 -B replay_two_input_first_points.py | cmp - EXACT-TWO-INPUT-FIRST-POINTS.json)
(cd cold && sha256sum -c SHA256SUMS)
```
