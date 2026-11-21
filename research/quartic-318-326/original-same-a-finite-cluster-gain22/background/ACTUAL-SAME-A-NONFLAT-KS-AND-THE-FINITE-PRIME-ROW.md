# Nonflat specialization of the actual polarized Kodaira–Spencer map

The finite input of the literal 318/326 reverse concerns the **same** original selected polarized quaternionic surface \(A/L\). At every finite place of its one auxiliary height field, the two original rational tensors
\[
x_i=\Psi_L^{-1}(210 S_i),\qquad
S_0=32D_0^2 Q,\quad S_1=D_0^2tQ,\quad
Q=(dt)^2/\prod_j(t-b_j)
\]
must have primitive-lattice norm at most 1. Here \(t=32u/v\), the contacts are \((0,32,-343,76832)\), \(D_0=2765952000\), and \(\Psi_L\) is the **particular** squared-determinant map also used at infinity. We produce the exact finite row, including at a node. This is a classical proof with a precise native handoff.

## 1. The actual identity Hodge module after arbitrary base change

Write \(X=X_N^{\rm full}\) over \(S=\operatorname{Spec}\mathbf Z[1/N]\) for the genuine fine PEL model, \(\pi:\mathcal A\to X\) for its genuine universal abelian scheme, \(e\) for the actual zero and \(\lambda:\mathcal A\to\mathcal A^\vee\) for the fixed principal polarization. Use \(N=3\) unless \(w\mid3\), then \(N=11\). Let \(g:T=\operatorname{Spec}R\to X\) be the proper integral extension of that actual fine mark over \(R=\mathcal O_{L,w}\). The pulled family is the prescribed good model of the same \(A\), hence its Néron model over this trait. No flatness of \(g\) is posited.

Set \(\mathcal W=e^*\Omega^1_{\mathcal A/X}\), \(H=\det\mathcal W\). Ordinary relative Kähler base change gives \(g^*\mathcal W=e_T^*\Omega^1_{\mathcal A_T/T}\). This is exactly the affine conormal module: over an actual zero neighborhood with base algebra \(C\), total algebra \(B\), true augmentation \(\epsilon:B\to C\) and \(I=\ker\epsilon\), the identification is
\[
 I/I^2 \longrightarrow C\otimes_{B,\epsilon}\Omega^1_{B/C},\qquad
 [b]\longmapsto1\otimes db\quad(b\in I).
\]
Its inverse is induced by the \(C\)-derivation \(b\mapsto[b-\epsilon(b)]\) into \(I/I^2\), with \(B\) acting through \(\epsilon\). The Leibniz defect is a product of two elements of \(I\); the two compositions are the identities on the displayed generators.

For \(B_R=R\otimes_C B\) and \(J=\ker(B_R\to R)\) of the actual scalar-extended augmentation, the nonflat conormal map on pure tensors sends \(r\otimes[b]\) to \([r(1\otimes b)]\). Under the Kähler identification this sends \(r\otimes(1\otimes db)\) to \(r(1\otimes d(1\otimes b))\), with derivative relative to \(R\). Thus the two identifications agree *before* taking determinants. Two chosen affine neighborhoods restrict at the same actual identity stalk to the same intrinsic \(e^*\Omega\); localization of the conormal is not a new frame. The archived 78a894d9 owner checks the augmentation kernel and flat conormal comparison; the unchanged 8b7630ed candidate proves the arbitrary-base conormal comparison. Neither source implements the geometric or cohomological identification below.

## 2. Pull the extension, rather than rebuild an absolute sequence on the trait

Let \(D=\omega_{X/S}\) be the relative dualizing line and \(c:\Omega^1_{X/S}\to D\) the actual fundamental map used by Yuan. Since \(\pi\) is smooth, the transitivity sequence of \(\mathcal A\to X\to S\) is short exact even when \(X/S\) is not smooth, by [Stacks Lemma 29.35.16](https://stacks.math.columbia.edu/tag/01V4). Its quotient \(\Omega^1_{\mathcal A/X}\) is locally free. If \(j\) is the inclusion of the left term, push out by \(\pi^*c\):
\[
 E_D=(\Omega^1_{\mathcal A/S}\oplus\pi^*D)/
             \{(j a,-\pi^*c(a)):a\in\pi^*\Omega^1_{X/S}\}.
\]
The resulting sequence
\[
 0\to\pi^*D\to E_D\to\Omega^1_{\mathcal A/X}\to0                  \tag{1}
\]
is locally split as a sequence of modules, since the quotient is locally free. Therefore its pullback along \(\mathcal A_T\to\mathcal A\) is again short exact for **arbitrary** \(g\). Its endpoints are \(\pi_T^*g^*D\) and \(\Omega^1_{\mathcal A_T/T}\). This does not assert \(g^*D=\Omega^1_{T/S}\): the latter has zero generic fibre for this number-field trait, while \(g^*D\) has rank one.

Invariant translation gives \(\Omega^1_{\mathcal A/X}\simeq\pi^*\mathcal W\), and \(\pi_*\mathcal O=\mathcal O\) universally by [Stacks Lemma 36.32.6](https://stacks.math.columbia.edu/tag/0E0L). Local trivialization of the line \(D\) gives \(R^1\pi_*(\pi^*D)=R^1\pi_*\mathcal O\otimes D\); no projection formula for a nonfree nodal \(\Omega^1_{X/S}\) is needed. For the other endpoint use [Liu–Lorenzini–Raynaud, Proposition 1.3](https://math.stanford.edu/~conrad/BSDseminar/refs/BSDAT.pdf#page=7) and [Lan, Theorem 1.3.2.3](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf). The rigidified dual Picard functor commutes with arbitrary base change by its definition on test schemes, with the identity-component condition on geometric fibres. Its tangent comparison identifies \(H^1(\mathcal A_U,\mathcal O)\) on each affine \(U\) with the sections of \(\operatorname{Lie}\mathcal A^\vee\). This yields the actual, not merely rank-preserving, base-change isomorphism: a cocycle \(a_{ij}\) gives the first-order line bundle with transitions \(1+\varepsilon a_{ij}\); pullback applies the same substitution to each \(a_{ij}\). The infinitesimal bundle reduces to the trivial bundle, so lies in the tangent to the dual Picard functor. This invokes no Picard flatness for an arbitrary family.

To compute the connector choose an affine open in the base and a finite affine cover of its restricted proper separated family. Finite intersections of its affine opens are affine over the affine base, and after pullback the same holds. Lift the invariant form on every affine to \(E_D\), using exactness of affine quasi-coherent sections. Its fixed ordered differences are the cocycle in the left endpoint. Those same differences after scalar substitution compute the connector of the pulled sequence. Both endpoint comparisons above are actual isomorphisms, so
\[
 g^*\phi_D=\phi_{D,T}:\mathcal W_T\to
             \operatorname{Lie}(\mathcal A_T^\vee)\otimes_R g^*D .
\]
No commutation of arbitrary higher direct images of \(E_D\) with nonflat pullback is assumed.

## 3. Identify the literal Yuan map, then normalize on the model

The connector of (1) is Yuan's \(\phi_2\): on the smooth locus it is the cotangent connection via the ordinary differential-to-dualizing identification. The two maps between locally free modules agree on the generic fibre and hence coincide on the original flat arithmetic model. The determinant, tensor pairing with the dual determinant and the specified principal \(\lambda\) are exactly those in [Yuan §1](https://arxiv.org/html/2205.11334v2#S1). All commute with base change of the vector bundles. Consequently the trait computation recovers \(g^*\Psi\) for **that** \(\Psi=\psi_3:H^{\otimes2}\to D^{\otimes2}\), using the ordered wedge of the identity module in §1. The two actual finite étale 33-level comparisons transport this same map, and on the common generic fibre the ordinary noncontact \(dt\) is the one in the archived complex computation. No separately chosen dual map, square frame or \(dt\) is substituted.

Yuan Theorem 1.1 identifies the exact integral image with \(210D^{\otimes2}\). Since 210 is a nonzerodivisor on the actual model, it gives the unique integral isomorphism \(\Theta:H^{\otimes2}\simeq D^{\otimes2}\) satisfying \(210\Theta=\Psi\). **First** divide on the original model, **then** pull to \(T\). For any primitive ordered wedge \(h\) of the actual trait Hodge module and generator \(\omega\) of \(g^*D\),
\[
 (g^*\Theta)(h^{\otimes2})=\eta\,\omega^{\otimes2},\quad
 (g^*\Psi)(h^{\otimes2})=210\eta\,\omega^{\otimes2},\quad \eta\in R^\times.       \tag{2}
\]
The primitive coefficient of \(\Psi_T\) therefore has additive valuation \(v_w(210)=v_w(p)\) at \(p\in\{2,3,5,7\}\), and zero otherwise. If \(v_w(\varpi_w)=1\), this is the actual ramification index at the four primes, not uniformly 1. Reducing the raw map at such a place may kill all of \(\Psi_T\), while \(\Theta_T\) is still an isomorphism. One cannot normalize the reduced raw matrix or recompute quaternionic invariant Hom in the trait to obtain it.

## 4. Exact finite row consumed by the published reverse

Both literal \(S_i\) are integral on the original regular semistable models. Recall the finite check: in an original vertical height-one stalk the residue prime is a uniformizer by reducedness. The fundamental differential in a local dualizing frame preserves that DVR and kills its uniformizer, hence \(v(df)\ge v(f)\). If \(v(t)<0\), all \(v(t-b_j)=v(t)\) and both \(Q\) and \(tQ\) are integral there. Otherwise if \(a\le b\le c'\le d\) sort the four depths, the first three are at most \(v(D_0)\) by the differences of the four contacts. The largest root gives \(v(dt)\ge d\), so \(v(Q)\ge d-a-b-c'\ge-2v(D_0)\). Multiplication by \(D_0^2\) clears it. The actual index-two branches give horizontal integrality, also at infinity where \(t=z^{-2}\) gives orders 2 and 0 for \(Q\) and \(tQ\). Extension from height one on the regular original model gives the global sections. These are the exact \(+64\) paper tensors with 32 in \(S_0\); the nearby native convention moves that 32 to the scalar ratio instead.

Write \(g^*S_i=a_i\omega^{\otimes2}\), with \(a_i\in R\). Equation (2) gives the exact coefficient \(a_i/\eta\) of \(x_i\) in \(h^{\otimes2}\), with valuation \(v_w(a_i)\). For the same globally selected rational Hodge determinant \(H_0\) write \(h=\rho H_0\). Its coefficient in \(H_0^{\otimes2}\) is \((a_i/\eta)\rho^2\). The primitive Néron lattice gives \(|\rho|_w\|H_0\|_w=1\). Thus the required bound is the actual equality
\[
 \bigl|\operatorname{coeff}_{H_0^{\otimes2}}(x_i)\bigr|_w\,\|H_0\|_w^2
       = |a_i|_w\le1 .
\]
It holds at all finite places of the same \(A/L\), including nodal specializations and residue 2, 3, 5, 7. There is no different, extra factor of 210 or independent representative of either section. The archimedean factor 210 under the unnormalized isometry and the strict reverse constants are unchanged. The chosen generic point specializes actual rational **sections** nonpolar there; no map of the entire function field to \(L\) is used.

The concrete next native input is (1) on the actual family, its conormal/differential identification, and the represented-Picard \(H^1\) base-change comparison for that family, joined to the existing Čech connector. Once (2) is produced from the actual normalized map, the finite norm row requires neither arbitrary height inputs nor flatness of evaluation. This paper does not modify the archived green owner or the staged 2/0 candidate. It is about \(A\), not the distinct modular Jacobian \(J\), and makes no native reverse claim.
