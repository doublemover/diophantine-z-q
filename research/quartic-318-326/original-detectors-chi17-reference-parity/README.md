# Exact dyadic depth of the weighted reference at D = −119

Start with [the proof](proof/EXACT-D119-WEIGHTED-SEED-IS-ODD.md) and the
[independent exact review](independent-review/INDEPENDENT-CHI17-D119-REFERENCE-PARITY-REVIEW.md).
Run 'sh verify.sh' for standard-library Python replay and byte comparison.

The calculation is on the fixed weighted E₋₁₇ curve, not either target
unweighted twist. Ordinary level-16 specialization at 3 isolates the
complete ten-point tame CM orbit by a single irreducible polynomial.
The chosen genus-half torus norm has fourth power −1, so the resulting
weighted trace has odd rational free coordinate. Combined with the
prior exact height ratios, this pins both selected weighted traces
to depth ω(sᵢ)−1. It does not give a point on either target arm.

The two preceding sources used in the paper are the complete oriented
D = −119 pilot (checksum list c2ed5f8b, raw data SHA-256
8cfca028b915bd6c059853447faeb5c50bbee67f58ac4816e4b25f336bfcc85d)
and the exact both-arm weighted height comparison (checksum list
5410e6e8b97a25be8800e815b1d5f87673e1dd4d8002d2c5913d999182bb315f,
paper SHA-256 483151197fb6b24d7af227e73bd1af726c283b3c14a245e53faed83dc5f0d1b0).
The modular coordinates and their relative source references are
described in the proof. No donor code or file is required for this
polynomial replay.
