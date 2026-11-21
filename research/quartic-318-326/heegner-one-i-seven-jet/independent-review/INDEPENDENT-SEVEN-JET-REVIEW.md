# Independent cold review: seven-coefficient auxiliary-quadric search

Reviewed the exact packet with manifest
`4e874f58aec67ab996d57a39bc748bef9e5e35374d01a9bfff6bfdc2dca79d9d`,
paper `2d21c6cf425d496796c1d77f02086f1411f24a2354ac44ebb4940940bc5e7c4d`,
verifier `525fbe53e4b4d2ee221114de693cdf3fc91925c3edead90730103380d16d3b93`,
and complete depth-2 output
`2f361e49ed8d749db24b9bef96a233112f4eb5a709c9c678c56e9b4081d08735`.
All five entries in the author manifest passed, and the complete 3-worker
replay over all 3,776 tubes at 59² matched the frozen JSON byte-for-byte.

The two omitted monomial columns have rank two, so the eight retained
coordinates are a basis modulo the old degree-two ideal. Every nonzero
dual vector therefore defines a genuinely new quadric. For each smooth
normalized local residue, the same unit 2×2 derivative minor solves
the two dependent coefficients mod N^(7−j); the polar expansion has no
unjustified division, and the displayed zeroth coefficient plus six
nonconstant coefficients is sufficient mod N^7. Hensel uniqueness
then covers each entire tube. The actual integer projective pivot
rescales the eight monomial values by its square. The additive span of
the seven value vectors consequently has at most N^28 residues out of
N^56 and the primal evaluation lattice index is at least N^28. For
the exact dual normal, the tested integral pairing and strict bound
B²·||λ||₁ < N^7 give a valid height cutoff. The dimension-eight LLL
bound yields the stated sufficient inequality N^28 > 2^26 B^16,
hence O(B^(4/7) polylog B) for this fixed curve with exact
fixed-dimension, bounded-degree rational solving. The method is
related to the p-adic method described in Fisher's
[6- and 12-descent paper](https://arxiv.org/pdf/0711.3774), end of §6.1;
§6.2 in the arXiv version begins the flex-matrix construction.

At 59² the computation verified 3,776 distinct auxiliary quadrics and
uniform height 949470. It excluded 3,772 through modular screens and
four by exact characteristic-zero rational section tests; one of those
four was a forced rerun of a section already excluded by a modular screen.
The degree-eight section argument uses the integral degree-four curve and
a quadric outside its ideal. The exact solver tested every last-nonzero
projective chart, including infinity, not only affine product points.
The entire specified finite union has no rational points; it follows
that the exact reduced marked cover has none of primitive sup height at
most 949470. This does not bound the height of a hypothetical larger
rational point and does not settle the original mark, rank, companion,
or any theta residue. The selected 128-tube pilot is not global coverage.

No Lean, remote writes or external arithmetic oracle.

— high_review_ci
