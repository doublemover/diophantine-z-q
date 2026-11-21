# The ordered Abel differential and its actual target Haar measure

Paper proof. The Jacobian throughout is the Jacobian \(J_X\) of the actual
smooth projective curve \(X\), after the chosen embedding into \(\mathbf C\).
It is not the separate abelian variety \(A\) used elsewhere. We do not replace
the actual Abel map by a map into an unrelated torus or only an isogenous
Jacobian.

## 1. Make the logarithm coordinates from the same algebraic forms

Let \(p_*\in X(\mathbf C)\), put \(J=J_X(\mathbf C)\), and write
\(a(p)=[p-p_*]\) for the actual Abel map. Let
\((\omega_1,\ldots,\omega_g)\) be the ordered algebraic differential frame
whose period rows and determinant are being compared, at this embedding.
By [Milne, Jacobian Varieties, Prop. 2.2, pp. 6–7](https://jmilne.org/math/xnotes/JVs.pdf#page=7),
pullback along this \(a\) gives an isomorphism from invariant regular
differentials of the actual \(J_X\) to regular differentials on \(X\).
Consequently there is a unique ordered invariant coframe \(\eta_i\) on \(J\)
satisfying \(a^*\eta_i=\omega_i\). This is a theorem about the same Abel map,
not an independent identification of two spaces of forms. For \(g=0\) the
Jacobian and ordered zero-fold product are points; take the empty determinant
and their measures to be \(1\). Henceforth \(g>0\).

Write \(V=T_0J\) and use the complex linear coordinates
\(z_i(v)=\eta_i(0)(v)\) on \(V\). The exponential of this very \(J\), not of
another abelian variety, is a surjective holomorphic group homomorphism
\(e:V\to J\) with differential \(1\) at \(0\) and full lattice kernel
\(\Lambda\) ([Milne, Abelian Varieties, Prop. 2.1, pp. 10–11](https://www.jmilne.org/math/CourseNotes/AV.pdf#page=11)).
It is locally biholomorphic everywhere by translation.
The left-translation formula for a group homomorphism and the invariant
nature of \(\eta_i\) give \(e^*\eta_i=dz_i\) at every \(v\): both sides
are translation invariant and their values at \(0\) agree.
Thus the target coframe used in local coordinates is fixed by the *actual*
algebraic forms, with no linear reframe or scale to choose.

In the ordinary period chart of the same modular curve, define
\(f_i(\tau)\) by \(\pi^*\omega_i=f_i(\tau)\,d\tau\), where \(\pi\) is the
actual ordinary period projection. This specifies which analytic functions
may be fed to the existing ordered Gram construction. Deck invariance and
\(\gamma'(\tau)=(c\tau+d)^{-2}\) give the weight-two transformation. At a
cusp of width \(w\), if \(\omega_i=h(q_w)dq_w\) in a holomorphic coordinate
\(q_w=\exp(2\pi i\tau/w)\), its coefficient in \(d\tau\) is
\((2\pi i/w)q_w h(q_w)\). It therefore vanishes at that cusp in the
appropriate slash chart. In particular a coefficient expressed first
against \(dq_w/q_w\) is not silently treated as its coefficient against
\(d\tau\); the factor \(2\pi i/w\) belongs to the same \(f_i\).
This argument uses the actual ordinary uniformization and cusp disks of
the selected compactification. Those analytic identifications are not
constructed by the Lean measure modules.

## 2. The derivative of one local lift, then the literal ordered sum

At any ordinary period \(\tau\), shrink to an injective period disk \(B\)
and an actual inverse chart of \(e\) containing \(a(\pi(\tau))\).
Let \(b:B\to V\) be the resulting local lift of \(a\circ\pi\).
Then
\[
d(z_i\circ b)=b^* dz_i=(a\circ\pi)^*\eta_i
=\pi^*\omega_i=f_i(\tau)\,d\tau.
\]
Equivalently, \(z_i\circ b\) is the holomorphic primitive of the exact
coefficient \(f_i\) on the disk, plus its integration constant. Another
local lift changes only a constant element of \(\Lambda\). The argument
uses a one-variable lift of the actual *degree-one* Abel map, not a
premise about the derivative of an ordered \(g\)-point map.

Let \(F:X^g\to J\) be the algebraic map \(F((p_j))=\sum_j a(p_j)\).
For a tuple of ordinary periods choose one lift \(b_j\) as above in each
factor. Since \(e\) is a group homomorphism, \(\sum_j b_j(\tau_j)\)
is a lift of \(F\circ\pi^g\). On a sufficiently small connected product of
disks, any chosen target logarithm of this \(F\) differs from this lift by
a constant vector in \(\Lambda\). Its complex derivative in the ordered
tangent columns is exactly
\[
D F_\tau=(f_i(\tau_j))_{i,j}.
\]
There are no extra \(g!\), \(2\pi\), or Haar factors in this derivative.
Changing from row-vector to column-vector convention transposes this
matrix and does not change its determinant. The two-owner native
SelectedActualAbelPointwiseDerivative318 packet is the coefficientwise
chain-rule / finite-sum / determinant step and calls the strictly checked
local complex Jacobian theorem with this derivative; it does not yet
construct the algebraic Abel map or its analytic logarithms.

## 3. Construct the unnormalized measure of the same \(J\)

Use standard Euclidean measure \(m\) on \(V\cong\mathbf C^g\) in these
very \(z_i\)-coordinates. Pick a real basis \(\lambda_1,\ldots,\lambda_{2g}\)
of \(V\) which is a \(\mathbf Z\)-basis of the actual lattice \(\Lambda\).
Let \(P=\{\sum t_i\lambda_i:0\le t_i<1\}\), and define
\(\nu=e_*(m|_P)\). The half-open translates \(P+\lambda\) partition \(V\)
exactly. This definition does **not** divide by \(m(P)\).
It identifies the mass as
\(\nu(J)=m(P)=|\det_{\mathbf R}(\lambda_1,\ldots,\lambda_{2g})|\).

For an open \(W\subset V\) on which \(e\) is injective let \(U=e(W)\).
For a Borel set \(A\subset U\) put \(W_A=(e|_W)^{-1}(A)\). Then
\[
\begin{aligned}
\nu(A)
 &=\sum_{\lambda\in\Lambda}m\bigl(P\cap(W_A+\lambda)\bigr)\\
 &=\sum_{\lambda\in\Lambda}m\bigl((P-\lambda)\cap W_A\bigr)
 =m(W_A).
\end{aligned}
\]
Indeed all sets of the first sum are disjoint by injectivity on \(W\),
and those in the last sum partition \(W_A\). Thus every actual logarithm
chart identifies \(\nu|_U\) with Euclidean measure, not a Haar measure up
to an unspecified constant. It follows by covering \(J\) with countably
many such charts, and partitioning the cover measurably, that \(\nu\)
is translation invariant and independent of the chosen half-open lattice
basis. This also follows directly by applying the displayed identity
simultaneously to \(W\) and \(W+v\).

With \(\eta=\eta_1\wedge\cdots\wedge\eta_g\) the exact positive volume
form is
\[
d\nu=\frac{i^{\,g^2}}{2^g}\eta\wedge\bar\eta.
\]
In the same coordinate chart, reorder the \(g\) conjugate factors into
adjacent pairs, obtaining sign \((-1)^{g(g-1)/2}\);
\((i/2)dz_j\wedge d\bar z_j=dx_j\wedge dy_j\).
This proves the normalization, including the factor \(2^{-g}\) and
the complex orientation. One may thus read \(\nu(J)\) from the same
Hodge wedge or from the actual lattice covolume. No stand-in period
matrix, implicit probability normalization or sign is required.

## 4. Local sheet pushforward on the existing source measure

Assume the literal ordinary chart comparison above, not a newly chosen
analytic copy of \(X\). On an injective upper-half-plane period rectangle
\(B=\prod_j B_j\), the exact single-period quotient restriction is the
pushforward of the actual upstairs hyperbolic restriction. Taking its
ordered product yields the same quotient product area used by Abel9.
On \(B\) the invariant quotient weight in Abel9 is
\[
 \left|\det(f_i(\tau_j))\right|^2\prod_j(\operatorname{Im}\tau_j)^2 .
\]
The upstairs reference densities are exactly
\(\prod_j(\operatorname{Im}\tau_j)^{-2}\) times the usual complex product
Lebesgue measure. They cancel on the given rectangle and on every Borel
subset of it. Thus the source weighted measure in a literal lift of
\(B\) is \(|\det DF|^2m\). This is the precise identity represented in
the weighted-period-product source candidate; the individual packet
status is tracked separately from this proof.

Let \(G\) be the complement of the images of the critical locus of \(F\)
and of the finitely many discarded-coordinate slices of \(X^g\).
Compactness of \(X^g\) makes the complement closed, hence \(G\) open.
Its two excluded images are null: equal-dimensional Jacobian nullity
for the singular determinant locus, and differentiable propagation of
nullity from each discarded slice (complex codimension one) in local
product coordinates. The exceptional weighted source is null as well:
its critical part has zero determinant weight, and its remaining part
is covered by countably many local diffeomorphisms on which the
weighted change-of-variables formula pulls back zero target measure.
None of this asserts that any distinguished arithmetic value is in \(G\).

For \(y\in G\), its compact fibre is nonempty by Riemann–Roch for the
degree-\(g\) line class given by \(y+g p_*\). The derivative is invertible
at every point of that fibre. A repeated coordinate would give
proportional evaluation columns in local coordinates, hence a singular
derivative; thus an ordered preimage represents a reduced divisor \(D\).
The invertible evaluation map implies \(H^0(K_X-D)=0\) and
Riemann–Roch gives \(h^0(D)=1\). That divisor is the unique effective
representative of its line class, so there are exactly \(g!\) ordered
preimages. This also avoids needing an independently assumed
topological degree or smoothness of the whole map.

At such a \(y\), take disjoint inverse-function neighborhoods of all its
preimages, each contained in one of the ordinary period rectangles of
the original quotient. Shrink the target neighborhood inside one
logarithm chart and inside each of their images and outside the image
of their compact complement. Then the whole preimage of the resulting
open \(U\) consists of \(g!\) disjoint genuine sheets. On each sheet,
the coordinate Jacobian, the source identity above, and §3 give
\[
 F_*(\mu_{\mathrm{Abel}}|_{S_j})=\nu|_U.
\]
The source and target scales have both been constructed, so this is not
an assumed matching of transported measures. Use a countable subcover
of \(G\) and the two null complements to deduce
\(F_*\mu_{\mathrm{Abel}}=g!\,\nu\).
This is exactly the global measure equality used by the existing Gram
argument, with the Abel points still ordered.

**Native boundary.** This note proves the geometric bridge on paper
given the actual modular uniformization of the selected curve and the
algebraic \(J_X,a\) (as in the preceding actual normalization/lattice
work). The native source now separates canonical inputs from proved
identities: actual degree-one lifts in the original cusp-form basis,
actual target torus local Haar, true ordinary/compact inclusion,
topological sheet decomposition, the source chart measure computation,
and the local Jacobian. It does not claim the missing geometric data
are already all constructed in Lean, nor any arithmetic height bound.
