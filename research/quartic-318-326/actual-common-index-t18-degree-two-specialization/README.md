# A degree-two specialization of the fixed input-zero secant

For the fixed first point at `t=18`, this independently reviewed [paper](author/COMMON-INDEX-T18-DEGREE-TWO-SPECIALIZATION.md) gives an explicit rational degree-two family in the scalar parameter and shows that odd-degree rational specializations cannot supply a section. The explicit family meets the already-controlled scalar local neighborhoods. No exact match to the scalar at an actual common index, nor any of the four PointPairs, is supplied.

The [independent review](cold/INDEPENDENT-T18-DEGREE-TWO-SPECIALIZATION-REVIEW.md) binds the unchanged source and replay:

```sh
sha256sum -c SHA256SUMS
(cd author && sha256sum -c SHA256SUMS &&
  python3 -B replay_degree_two_specialization.py | cmp - EXACT-DEGREE-TWO-SPECIALIZATION.json)
(cd cold && sha256sum -c SHA256SUMS)
```
