# Independent review: the exact arithmetic D=210 four-root cover

Reviewed `original-d210-arithmetic-four-root-constants-r1/SHA256SUMS` SHA-256
`0eac4b676e75fc28e602a70967fb5f1d811195f70d61334224121ff67378aa9b` and
`EXACT-ARITHMETIC-D210-FOUR-ROOT-COVER.md` SHA-256
`c241485d42ae79d270bd9eb23e9bd9e3b5bb5580ea6fd7862535d6542de6d471`.
All author bytes and the finite replay matched; a separate exact rational calculation independently recovered the branch normalization, kernels, and constants.

**Verdict.** The four twists are exact over \(\mathbb Q(t)\), on the actual original quotient coordinate \(t=32s\), relative to the five isomorphism identifications in [Padurariu–Saia, arXiv v2, Theorems 1.2(1), 6.2 and Table 2](https://arxiv.org/pdf/2509.25368v2), not just to their isogeny classes or geometric \(j\)-invariants. The four fields have radicands
\[
 -14t,\qquad -6(t-32),\qquad 42(t-76832),\qquad -21(t+343).
\]

1. From the four [González–Rotger primary quartics, Theorem 4.2/Table 2](https://web.mat.upc.edu/victor.rotger/docs/ShimuraGenusOne.pdf) I independently recomputed the rational \(j\)'s and six anharmonic variants. With \(w_{210},w_{105},w_{70}\) at \(\infty,0,1\), the omitted-branch \(j\)'s select the unique pair \((2401,-343/32)\) for \(w_{42},w_{30}\). The rational effective elementary 2-group has cyclic geometric stabilizers, and the genus formula and Riemann–Hurwitz give precisely these five inertia orbits; the first four labels form a basis and their sum is \(w_{210}\). In the genus-one intermediate computations the translation subgroup quotient preserves geometric \(j\) (it is quotient by full 2-torsion); this step is used for branch labels only.
2. Independently generated all five rank-three kernels using prime-subset XOR and matched each to the exact table row: \(210b6,210c3,210a6,210e5,210d2\). None is among the ambiguity exceptions in the proof of Theorem 6.2. A surviving rational branch has one geometric ramification point and thus a rational point on the genus-one quotient. Taking it as origin identifies the curve with its *arithmetic* Jacobian and makes the nontrivial deck operator \([-1]\), so the Weierstrass abscissa supplies the invariant coordinate. No implicit quadratic twist remains at this step.
3. Freshly matched the five coefficient vectors to [Cremona's primary data, lines 787, 795, 800, 805, 812](https://raw.githubusercontent.com/JohnCremona/ecdata/master/allcurves/allcurves.00000-09999). Completing the square gives the three finite cubic roots and the exact affine comparison in the first four rows. The last row uses \(x=A/t+B\), so the correct signed constant is \(-A^3/(b_1b_2b_3)\) after replacing \(Y\) by \(t^2Y\). The five squareclasses are \(3,7,-1,2,-42\). Multiplying each finite triple class by the last full-product class gives the four displayed constants; their products match the five square factors with common square \(42^2\). The dual inertia characters generate the full geometric group and hence the whole degree-sixteen arithmetic cover.

This identifies the same generic coarse curve over \(\mathbb Q\). It does not identify an integral or fine PEL model, select an orientation of all dependent roots independently, or prove any KS, height, good-reduction or Lean statement. Independent mathematical/source cold review: high_review_ci.

