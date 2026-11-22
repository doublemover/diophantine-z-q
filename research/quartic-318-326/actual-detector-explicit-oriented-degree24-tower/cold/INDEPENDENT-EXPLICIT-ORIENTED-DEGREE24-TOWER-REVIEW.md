# Independent review: explicit oriented degree-24 defining tower

**PASS (mathematical proof and exact portable replay).** This receipt applies only to the following frozen author files.

| File | SHA-256 |
|---|---|
| Author `SHA256SUMS` | `da2d20edde432fc30c6ee312460c23e4450a33bc1d3a4b9cacbc7e2e39a87228` |
| `EXPLICIT-ORIENTED-DEGREE24-TOWER.md` | `60b9e6d265ee5e802042b970dfd2bb766b287791c21d18c73377ef9937c58319` |
| `replay_explicit_tower.py` | `7055469b1cfc5028adfe0f514b2e4f71a1abba6d72894132f5568b2a71e7fae9` |
| `EXACT-EXPLICIT-TOWER-CONTROLS.json` | `d783cae7b41c6881f4f401bbdd91439d54215dc8cc9f72d83e8713ff25c53181` |

I independently reduced the exact stock doubling relation modulo its two-abscissa quadratic and eliminated the product variable. I checked the sextic sign, the alternate polynomial product, and the quadratic norm identity. Since the product is determined by the sum and the two abscissas identify the same 5-line, the six transitive lines give the fixed degree-six field. This uses the previously established full residual image from the published criterion.

The determinant correction is necessary: with scalar `b` on the kernel line and cyclotomic determinant `e`, the specified covector convention is `a = e/b`. Thus the product of the abscissa difference with the cyclotomic square root of 5 transforms by `a²`, identifying the actual covector half-field rather than the point half-field. The independent scalar and determinant characters give the disjoint quartic point and cyclotomic subfields over the line field and rule out a zero final radical. I checked the tangent sign, the defining square, the direct quartic, and the action on the twisted radical: the lift with `b = 1, e = 2` is the covector scalar 2, not 3, and its square negates the radical. The lift fixing the twist square root is justified by the original disjointness at 17.

From a fresh copy the author's whole checksum list and standard-library replay matched the exact JSON. An independent point and cyclotomic-field calculation checked all four nonzero rational 5-torsion points at each of 31, 71, 101, 271, 127 and 157, including literal arithmetic Frobenius at 127 and 157 and the named vectors at 127.

This is a defining-tower and generator result for the existing one-companion criterion. It supplies no selected numerical `n`, class-group computation, eigenspace dimension or bound, Mordell–Weil rank, mark, or point. The finite-field controls check the fixed equations and orientation, not the Selmer certificate for a selected companion.

Signed: independent original-quartic reviewer, 2026-11-22.
