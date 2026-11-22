# Independent review: degree-two t=18 secant specialization

**PASS for the exact rational-family and period-two proof, with fixed arithmetic replay.** This receipt binds:

| File | SHA-256 |
|---|---|
| Author `SHA256SUMS` | `a279f569bceffba23bbc6a7ff257cdd6ad01f89960bf6925beec3f59b7c51200` |
| `COMMON-INDEX-T18-DEGREE-TWO-SPECIALIZATION.md` | `b9bc55710649b8f290f128634d88b08c939bc1b6f73b02e1f9818d791ad0a969` |
| `replay_degree_two_specialization.py` | `385fab59c4b838e00ed4595a3f1efb80bda6dbf9a8f533073114318c48eb5382` |
| `EXACT-DEGREE-TWO-SPECIALIZATION.json` | `92f69033c5410ee5c0c13be468c2a0fc15bafc061416e4421aebd3926e95cbb9` |

The common-index preparation and fixed secant are the exact prior inputs: author lists `9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5`, `173d6f342c7a87f71430fe6cb7b2799cc02da878f771095c55cef238d6f3c158`, and `e3c9390760080729456a6926e61552a7883aa939ca84ac8156e31a2846782d37`. I verified the rational conic parameterization and its inverse, coprimality of the homogeneous numerator and denominator, the exact additional scalar square test for this family, and the simple geometric zeros of its complement. The standard-library replay matched the full frozen JSON. The dyadic correction after dividing by the square center has depth four, the ternary correction has depth three, and at each fixed beta prime the correction has positive depth with a unit center. These show that the family can approximate the prepared scalar at the listed places and at infinity. They do not put any chosen rational value, or its complement squareclass, into the actual discrete sequence at the eventual common index. The additional square test is sufficient for the secant, not necessary for arbitrary secants.

For the generic obstruction, I checked the nonsquare untwisting over the rational conic and descent of constant genus-one points. A descended rational point, including at the projective boundary, would be fixed by the sign involution. Its finite fixed points are all nonrational and its two infinity points are exchanged. The rational infinity points after untwisting show the nonzero torsor class is killed by two. Restriction and corestriction therefore prohibit a section after any odd-degree rational-function pullback, whereas the exact degree-two family does supply one. This is a generic rational-base obstruction and not an exclusion of points on individual specializations.

No common index, actual Gaussian key, actual complement, rank, mark, or PointPair is supplied. The other three detector PointPairs remain separate same-index requirements. No native Lean result is asserted.

Signed: independent original-quartic reviewer, 2026-11-22.
