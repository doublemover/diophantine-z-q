# Independent exact audit: birational Atkin coordinates and finite aliases

Signed: Vesper, independent reviewer of the marked finite computations.
2026-11-21 UTC. The two input results are complementary, not a
claim of separation or efficient reconstruction.

**Exact sources.** The two-coordinate field proof is bound by
manifest `cbb41d8db7a9579e4a2f655a3427a28e7ca5c4243c8f6f89db1abbf15ece5f7d`
(note `cb5642ab31f15f9ba805306231ae2352bdf343416318e0f8877a3694bcbd3f51`).
Hom's finite marked calculation is bound by
`0feb0ab7e157c9e1c8d952ddc8bc9aaf78900e176360e3b8a46a4af10d265303`
(note `f8016a0bc2dc895545f4963c43529049b7a31f863e830a5b9d121953c27169cb`).
All source hashes and both finite output JSON replays verified.
The field proof was independently cold-reviewed by its non-author Hom.

**Function field.** For the all-negative Atkin character and its
2-sign flip, canonical rational eta products have exactly trivial
extra Atkin phase. The local Γ₀(4) multiplier check at each odd
prime, plus full Fricke, controls the actual sign also at 2.
Reciprocal sums give pole degrees 1,726,560 and 5,179,680 at
the unique quotient cusp; their leading difference after cubing
has degree 5,179,679 and coefficient 4. Plain discriminant
products yield the same coprime-degree argument with initial
orders multiplied by 24 and leading coefficient 96. At other
points these products are units before taking sums. The rational
cusp is the unique place over its restriction and has residue
degree one, hence coprime valuation indices imply degree one
of the function-field extension. The assertion survives the
good tame reduction, including 13. No plane equation or weight-two
ratio is part of the proof.

**Finite, genuinely marked values.** Hom's actual returning
Vélu isogenies identify the full maximal order of discriminant
13. Its action on every tame torsion is computed in a valid
local basis. The subset circuit switches to the dual **image**
line at the used prime and transports the original other marks.
This gives intrinsic canonical W-orbit labels independently of
the discriminant values. On the complete fixed-six/variable-2399
slice there are 2,400 distinct W-orbits; all 127 symmetric
discriminant characters produce only 2,394 tuples. Each of the
six aliases persists even with the whole oriented tuple modulo
one common W-action. The order-14 tangent character calculation
explains why the normalized product of another even-weight
scalar on the same source cannot resolve them; the exact c₄
checks agree. These statements are for this controlled slice,
not the entire supersingular marked set.

**Exact extra replay.** The accompanying bounded check uses
the same authenticated actual endomorphism/mark circuit, but
reads the two plain discriminant coordinates corresponding
to the smaller eta pair (negative-sign masks 127 and 126).
It finds all 16 possible scalar pairs and retains all six
aliases; the genuine labels 521 and 1601 for example both
give (10,7). The accompanying JSON includes all bucket counts,
five exact canonical marked control keys and a digest of the
full rows. This is a separate readout of the existing finite
geometry, not an independent implementation of the geometry.

A birational plane image may identify special points; its
normalization/marked local data are still required there.
No guessed 24th root of a discriminant value evaluates
the q-normalized eta unit. Neither packet constructs a
marked weight-two ratio R, a selected CM fibre/cubic
torsor value, a production jet, or a rational point.

Replay from the author donor's exact script path:
```sh
python3 -B check_actual_eta_pair_discriminants.py /path/to/check_sparse_atkin_13.py | cmp - EXACT-ETA-PAIR-DISCRIMINANTS-13.json
sha256sum -c SHA256SUMS
```
