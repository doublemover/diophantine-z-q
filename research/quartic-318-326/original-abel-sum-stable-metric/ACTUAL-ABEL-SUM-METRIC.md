# The original stable metric from the actual Abel sum, without period matrices

Use the original smooth compact curve \(X=X_1(M)_L\), the fixed selected \(L\)-rational point \(P_0\) above \(J=1\), and the same Abel–Jacobi \(j_{P_0}:X\to J_X\) used for the integral Hodge pullback. No different function field, compactification, canonical basis, or normalization of \(J\) is used. In particular \(J_X\) is the Jacobian of this modular curve, not the arithmetic abelian surface \(A\) in the opposite inequality.

Fix a complex embedding \(s:L\hookrightarrow\mathbb C\), write \(C=X_s(\mathbb C)\), and let \(g=\dim J_X\). On this one complex fiber let \((\omega_1,\ldots,\omega_g)\) be the ordered invariant forms of the very same algebraic wedge in the height calculation. Put \(\eta_i=j_{P_0}^*\omega_i\), \(\Omega=\omega_1\wedge\cdots\wedge\omega_g\), and set
\[
 G_{ij}=\int_C\frac{i}{2}\,\eta_j\wedge\overline{\eta_i}.
\]
This ordering is conjugate first, exactly as in the original checked Petersson Gram. On the ordinary modular chart \(\eta_i=f_i(\tau)d\tau\), the literal cusp form already constructed on that chart. Since \((i/2)d\tau\wedge d\bar\tau=dx\wedge dy\), this agrees with integration of \(\overline{f_i}f_j y^2\) against \(dx\,dy/y^2\) on the modular quotient. The two measures are thereby matched with **no** group index or unnormalized area factor. Finite omitted points have zero area, and the regular \(\eta_i\) extend across them. This is the same \(G\), not a separately supplied Gram.

**Claim.** In the Gaudron–Rémond stable height convention, for this same wedge,
\[
 \|\Omega\|_{\mathrm{GR},s}^2=\pi^{-g}\det G.
\]
There is no need to construct \(a,b\)-cycles, two period matrices, an inverse of an \(a\)-period matrix, or a separate Riemann-bilinear assertion.

## The genuinely finite-degree map used in the integral

Use the actual algebraic Abel sum
\[
 a:C^g\longrightarrow (J_X)_s(\mathbb C),\quad
     (P_1,\ldots,P_g)\longmapsto\sum_{k=1}^g j_{P_0}(P_k).
\]
Its action on effective divisors is \(D\mapsto[D-gP_0]\). Translate \(\mathrm{Pic}^g(C)\) by \(gP_0\) to identify the target with \(\mathrm{Pic}^0(C)\). For \(g\ge2\), Riemann–Roch gives \(h^0(L')=1+h^0(K_C\otimes(L')^{-1})\) for a line bundle \(L'\) of degree \(g\). In particular every class occurs. The locus with \(h^0(L')>1\) is carried into the image of \(C^{g-2}\) under the effective-divisor map; this image is closed by properness and has dimension \(\le g-2\), less than \(g\). Outside it each fibre of the effective-divisor Abel map is exactly one divisor. The image in \(\mathrm{Pic}^g(C)\) of the diagonal locus in \(C^g\) is likewise closed and of dimension \(\le g-1\). Off both loci the unique divisor is reduced and has \(g!\) ordered lifts. Because the ground field is characteristic zero, \(a\) restricts over some nonempty Zariski open to finite étale of degree \(g!\). For \(g=1\) there is no residual or diagonal locus and the degree is one; for \(g=0\) both targets are the point and the assertion is \(0!=1\). This is the usual Abel inversion map; see [Milne, Jacobian Varieties, §5, Theorem 5.1](https://jmilne.org/math/CourseNotes/AV.pdf#page=140).

One must not claim the entire map \(a\) is finite. The good open suffices: outside it and outside its inverse image, the complements are proper complex algebraic subsets and have measure zero for smooth top forms. On the good open the map is a \(g!\)-sheeted holomorphic covering; each sheet preserves the complex orientation. A partition of unity and change of variables therefore give
\[
 \int_{C^g} a^*\nu = g!\int_{(J_X)_s(\mathbb C)}\nu
\]
for the smooth positive volume form \(\nu\) below. Both manifolds are compact. No choice of local ordering of an entire global sheet, or extension at a singular branch, enters this equality.

## The exact order, signs, and conjugation in the volume

For an invariant one-form on the commutative complex Lie group \((J_X)_s(\mathbb C)\), pullback by addition is the sum of its pulls from the factors. Indeed, translate tangent vectors to the identity and the derivative of addition becomes vector addition. Thus \(a^*\omega_i=\sum_k\operatorname{pr}_k^*\eta_i\).

Take local holomorphic coordinates \(z_k\) on the factors, so \(\operatorname{pr}_k^*\eta_i=f_i(z_k)dz_k\). Then
\[
 a^*\Omega=\det(f_i(z_k))_{i,k}\,dz_1\wedge\cdots\wedge dz_g.
\]
Each oriented pair \((i/2)dz_k\wedge d\bar z_k\) is \(dx_k\wedge dy_k\). Moving the conjugate differentials from grouped to interleaved order contributes \((-1)^{g(g-1)/2}\), and \(i^{g^2}=i^g(-1)^{g(g-1)/2}\). In particular, defining the positive real form \(\nu=(i^{g^2}/2^g)\Omega\wedge\bar\Omega\) gives
\[
 a^*\nu=|\det(f_i(z_k))|^2 \prod_{k=1}^g dx_k\,dy_k
\]
in product orientation. This sign also fixes the meaning of \(|\Omega\wedge\bar\Omega|=2^g\nu\). On overlapping product charts the formula is invariant: the square norm of each coordinate change transforms the corresponding area element. Alternatively choose one smooth positive area form on \(C\); the cross densities of \((i/2)\eta_j\wedge\bar\eta_i\) against it are global smooth integrable functions, so Fubini applies directly on the finite product with no global trivialization of \(\Omega_C^1\).

Expand the two determinants, conjugate sign first. Integration term by term separates by Fubini into the finite sum
\[
  \int_{C^g}a^*\nu
    =\sum_{\sigma,\tau\in S_g}\operatorname{sgn}(\sigma)\operatorname{sgn}(\tau)
       \prod_{k=1}^g G_{\sigma(k),\tau(k)}.
\]
For fixed \(\sigma\), put \(\rho=\tau\circ\sigma^{-1}\). The product reindexes to \(\prod_iG_{i,\rho(i)}\) and the product of signs is \(\operatorname{sgn}(\rho)\). Thus the inner sum for each \(\sigma\) is \(\det G\), giving exactly \(g!\det G\). The Gram has positive determinant since \(\eta_i\) are linearly independent holomorphic forms and the integral of the nonzero squared norm of each nonzero linear combination is positive.

Divide by the geometric degree to conclude \(\int_{(J_X)_s(\mathbb C)}\nu=\det G\). The original wedge's normalized norm is, by [Gaudron–Rémond, §2.3, Definition 2.1](https://ems.press/content/serial-article-files/43351#page=9),
\[
 \|\Omega\|_{\mathrm{GR},s}^2=(2\pi)^{-g}
   \int_{(J_X)_s(\mathbb C)}|\Omega\wedge\bar\Omega|
   =\pi^{-g}\det G.
\]
Thus \(-\log\|\Omega\|_{\mathrm{GR},s}=-\log\sqrt{\det G}+(g/2)\log\pi\), with the plus sign in the height and one average over all embeddings. The original Faltings convention of Gaudron–Rémond differs by subtracting exactly \((g/2)\log\pi\), not by a further choice of polarization or basis.

## Consequence for the original one-lattice height comparison

The finite contribution is unchanged. It comes from the same \(H=e^*\Omega^1_{\mathcal J/\mathcal O_L}\), same selected \(L\), same global generic Abel pullback and same coordinates on the selected original minor. The finite-Hom trace argument there supplies the original tests; localizing \(H\) supplies the local bases (no independent local choice is used in the height identity). With the displayed Archimedean equality, the intrinsic reference using the determinant of the original Petersson Gram is the GR height after adding exactly \((g/2)\log\pi\). Applying the original estimate yields \(h_{\mathrm{GR}}(J_X)\le g\log(1727M)\), and the same \(g\le M^2\) estimate. Neither statement transfers to \(A\) without the separate same-\(A\) modular/isogeny argument.

This is an alternate classical witness replacing the two period-matrix identities in the exact original modular height argument, not a new Lean proof of compact \(J_X\), construction of its Abel sum in mathlib, or a general integration theorem for complex differential forms. The finite determinant/Fubini component can be checked separately. The geometry interface of this route requires the literal Abel sum and its generic sheet number and volume pullback, not additional periods or Riemann bilinear relations.
