# Independent cold review: both actual weighted traces from one common prime

**PASS**, exact mathematical source and byte replay, 21 November 2026. Author
paper `483151197fb6b24d7af227e73bd1af726c283b3c14a245e53faed83dc5f0d1b0`;
author checksum list
`5410e6e8b97a25be8800e815b1d5f87673e1dd4d8002d2c5913d999182bb315f`.
The author hashes passed and the directed-graph replay matched its exact JSON.
The reviewed first-arm source `7af62937… / 96f6dd8f…` supplies the same
level-48, weighted genus-character and fixed-reference height comparison.

For each prime $t\mid\theta$, the fresh shared $r_t\equiv1\bmod24$
admits both prescribed edge signs by reciprocity, even for negative
$t\bmod4$. Its diagonal after removing $q_0$ is one in the first arm and
zero in the second since its only additional incidence is its own $t$.
Appending all reserves does not change the old contact or helper blocks.
In the second arm, the total $\theta$-incidence on each old $\beta$ row
is even. Actual 17-to-$\theta$ edges affect only the new block on removal
of 17, while the correction involving the 3-symbol of a new prime
belongs only to a new row. No symmetry hypothesis on the new block is
used. The same literal block-kernel proof works for the two distinct
matrices: the exact original sharp Selmer matrix and the recomputed
omitted-17 class-group Laplacian. The reserve equations kill the
$\theta$ variables, the old invertible block kills the old variables,
and the $\theta$ equations kill the reserve variables. When
$\theta=1$ this is the already reviewed first construction. All finite
conditions use one common $q_0$, not separate choices by arm.

The positive-twist parity formula and directed determinant in the
[tiling-number paper, Proposition 4.2(iii) and Theorems 2.7–2.8](https://arxiv.org/pdf/2405.11132)
apply to both $s_i\equiv7\bmod24$. The pinned first-arm formula via
[Cai–Shu–Tian, Theorem 1.1](https://arxiv.org/pdf/1408.1733#page=2)
then gives a nonzero $\chi_{17}$-weighted point from each arm on the
**same fixed** $E_{-17}$, and the stated two-adic free-index comparison.
The construction reselects the helper roster and common prime, not the
original protected detector data or any already fixed arithmetic
certificate.

This supplies no nonzero unweighted point, rank, or mark on a moving
target curve, no primitive Heegner coefficient, and no quartic endpoint.
No new Lean build or actual large CM orbit evaluated.

Signed: independent arithmetic and evidence reviewer.
