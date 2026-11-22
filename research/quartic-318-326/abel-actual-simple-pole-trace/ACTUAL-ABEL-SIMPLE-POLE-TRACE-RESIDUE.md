# The original ordered Abel degree by simple poles and the literal \(j\)-trace

Let \(X\) be the same proper smooth connected marked normalization \(X_1(M)_{\mathbb C}\), identified on complex points with the actual filled curve in its original ordinary period charts. Let \(J_X=\operatorname{Pic}^0(X)\) be its own algebraic Jacobian, with its actual pointed degree-one map \(a(P)=[P-P_*]\). The exact ordinary analytic identification of \(a\) uses its own normalized exponential, not a replacement torus. Let \(g\) be the genus, and write \(\omega_i\), \(1\le i\le g\), for the basis of global differentials obtained by pullback of the chosen invariant differentials on \(J_X\). These are independent by the pointed Abel pullback isomorphism ([Milne, *Jacobian Varieties*, §2 Proposition 2.2](https://www.jmilne.org/math/articles/1986c.pdf)). In the original period coordinate their readouts are precisely \(\omega_i=f_i(\tau)\,d\tau\). Write \(A:X^g\to J_X\) for the **ordered** algebraic sum of \(g\) copies of \(a\).

## 1. One actual reduced divisor with an invertible ordinary minor

Delete the finite designated locus of cusps and the literal \(j=0,1728\) fibres. On the remaining original period open, the coefficient vectors
\[
 (f_i(\tau))_{i=1}^g
\]
span \(\mathbb C^g\). Otherwise a nonzero constant linear combination of the \(\omega_i\) would vanish on a nonempty open of the connected compact Riemann surface, hence everywhere. Pick \(g\) vectors forming a basis. Their underlying points of \(X\) are distinct: at any one point a change of local uniformizer multiplies the whole evaluation column of a differential basis by one nonzero scalar. This gives a reduced effective divisor \(D_*\) of degree \(g\) on the actual marked curve, with invertible original period minor.

One can if desired choose \(D_*\) algebraic over a number field, without evaluating a numerical determinant or declaring any \(j=1\) point regular. The nonzero determinant persists on a product of pairwise disjoint small original neighborhoods. In each neighborhood the nonconstant map \(j\) is open; choose distinct values from the dense subfield \(\mathbb Q(i)\) in the resulting open subsets, then choose their preimages in those neighborhoods. Each such preimage is algebraic because \(j:X_1(M)\to\mathbb P^1\) is the same finite map on the arithmetic marked normalization. A finite extension contains the resulting finite set of points. The paper needs only existence and does not specify a numerical tuple.

## 2. No Riemann--Roch: the determinant kills the simple polar parts

This argument works for **every** ordinary ordered regular tuple, not just \(D_*\). Write its distinct underlying points as \(P_1,\ldots,P_g\) (as above, a repeated point cannot give an invertible minor) and put \(D=\sum_jP_j\). Suppose \(r\in\mathbb C(X)\) has poles bounded by \(D\). At \(P_j\), take the exact local period coordinate \(t_j=\tau-\tau_j\); the quotient projection is locally a chart at this actual ordinary point. Write
\[
 r=\beta_j/t_j+O(1), \qquad
 \omega_i=(f_i(\tau_j)+O(t_j))\,dt_j.
\]
The residue of \(\eta_i=r\omega_i\) at \(P_j\) is exactly \(f_i(\tau_j)\beta_j\). At every other point (including all cusps) \(\eta_i\) is regular because \(r\) and the actual global \(\omega_i\) are both regular there. No extension of a merely local form or choice of a parameter derivative at a cusp is assumed.

The sum of all these residues is zero. In this situation one can prove it using just the same finite \(j\)-map and rational partial fractions, as follows. On the literal generic marked field \(F=\mathbb C(X)\) write \(\omega_i=b_i\,dJ\) for \(J=j\). This is possible because \(F/\mathbb C(J)\) is finite separable (characteristic zero), so \(dJ\) is a basis of the generic relative differential line over \(\mathbb C\). The trace differential on the actual base is
\[
  \operatorname{Tr}_{F/\mathbb C(J)}(r b_i)\,dJ.
\]
On a punctured unramified base disc its germ is the sum of pullbacks along **all** local inverse branches of \(j\). Indeed the finite algebra over a generic point of that punctured region is the product of the evaluation fields in the inverse branches. The trace of multiplication in that product is the sum; equivalently the field trace agrees with this sum after scalars are extended to a splitting germ. There is no choice of one irreducible factor or one branch.

At any base value over which a point of \(X\) has ramification index \(e\), take \(u=J-b\) if the value is \(b\in\mathbb C\), and \(u=J^{-1}\) at infinity. Locally a coordinate \(t\) can be chosen with \(u=t^e\): any nonvanishing unit in the local expansion has a holomorphic \(e\)-th root on a sufficiently small centered disc, so this is an invertible local coordinate change. Write a meromorphic differential there as \((\sum_{n\gg-\infty}a_nt^n)\,dt\). The sum along the \(e\) punctured branches is
\[
\begin{split}
 \sum_{\zeta^e=1}\sum_n a_n(\zeta t)^n\,d(\zeta t)
   &=e\sum_m a_{em-1}t^{em-1}\,dt\\
   &=\sum_m a_{em-1}u^{m-1}\,du .
\end{split}
\]
The convergent Laurent expansions justify summation on the punctured disc. A regular source differential stays regular in this branch-cluster trace, a source simple pole contributes at most a simple pole, and its residue is exactly \(a_{-1}\), **not** \(e a_{-1}\). Summing over every cluster above a given base value thus sums exactly the corresponding source residues. At infinity the same computation uses \(u=1/J\) and \(dJ=-u^{-2}\,du\); because \(D\) has no cusp, every source differential is regular there, so the traced differential is regular at \(u=0\). This includes possibly ramified cusps and does not assert they have width one.

Consequently the rational coefficient in \(dJ\) has simple poles at most at the distinct finite numbers \(B=\{j(P_j)\}\), with residues \(c_b=\sum_{j:j(P_j)=b}f_i(\tau_j)\beta_j\). It is \(O(J^{-2})\) at infinity, since \(dJ=-u^{-2}\,du\). In rational partial fractions, the polynomial part is therefore zero, and
\[
 \operatorname{Tr}_{F/\mathbb C(J)}(r b_i)
   =\sum_{b\in B}\frac{c_b}{J-b},
 \qquad
 0=\sum_{b\in B}c_b=\sum_j f_i(\tau_j)\beta_j.
\]
This is also the top numerator coefficient of the partial fractions over the monic denominator \(\prod_{b\in B}(J-b)\), in degree \(|B|-1\). Coincident \(j(P_j)\)'s are grouped, not incorrectly counted as distinct poles.

Thus the same invertible matrix \((f_i(\tau_j))\) annihilates the column \((\beta_j)\), forcing all \(\beta_j=0\). Then \(r\) has no poles, so is constant on the compact connected curve. This proves \(H^0(X,\mathcal O_X(D))=\mathbb C\). Also \(H^0(X,\omega_X(-D))=0\) by injectivity of the evaluation matrix itself. These two exact facts for \(D\) are proved directly, not by invoking the Riemann--Roch dimension formula. In particular \(D_*\) is a reduced nonspecial degree-\(g\) divisor of the actual curve.

## 3. Full ordered fibres without constructing the symmetric power

The image of the **algebraic** ordered map \(A\) is closed in the Zariski topology. Indeed \(a\) and addition on \(J_X\) are algebraic, \(X^g\) is proper, and \(J_X\) is separated over \(\mathbb C\): the graph gives a closed immersion into \(X^g\times J_X\), followed by the proper projection. At the tuple producing \(D_*\), the ordinary invariant differential readout gives an invertible analytic derivative, with exactly the same minor. The inverse function theorem gives an analytic open in the image. An algebraically proper closed subset of the smooth connected, hence irreducible, \(J_X\) has empty analytic interior; this follows from holomorphic identity applied to local algebraic defining equations (equivalently from smaller complex dimension). Therefore the image is all \(J_X\). Every complex target has a complex source point: a nonempty finite-type fibre over the algebraically closed field \(\mathbb C\) has a \(\mathbb C\)-point.

Let \(G\) be the actual good target obtained by removing the image of the full closed bad source, as in the separately reviewed discarded-mask Sard proof. For \(y\in G\), choose any tuple in the nonempty fibre. Its divisor \(D\) is reduced and its matrix is invertible, so the preceding pole argument applies. **The single Picard principle used** is the definition of equality of divisor classes for this very \(J_X=\operatorname{Pic}^0(X)\): if another degree-\(g\) effective divisor \(E\) has the same pointed Abel sum, then \(\mathcal O_X(E-D)\simeq\mathcal O_X\), so \(E-D=\operatorname{div}(r)\) for some nonzero rational function on this same \(X\). Its poles are bounded by \(D\). It is constant and \(E=D\). This holds even if \(E\) was not initially assumed reduced. Hence the full ordered fibre consists exactly of the \(g!\) orderings of \(D\). No separate analytic connectedness of \(G\), generic symmetric power, Jacobi inversion theorem, or Riemann--Roch is used in this proof. Genus zero is the single-point source and target, with \(0!=1\).

## 4. Exact native boundary

The same marked compact source has pinned native normal-chart DVR attachments, and the existing original invariant-frame/period and ordered local derivative checks fix the evaluation matrix. The companion finite algebra extracts and groups the rational simple-pole residues and uses the coefficient in degree \(|B|-1\) to prove vanishing of the polar vector. It assumes the genuine trace differential readout; it does not claim Lean has constructed it. An actual general native theorem of residue comparison through all ramified marked stalks or a same-curve Picard-class equality theorem is not in the observed pinned dependencies. Neither full RR nor a scheme-level symmetric-power construction needs to be the future interface: one needs (i) literal same-point divisor/principal comparison for the given Abel map, (ii) principal-part/trace readout on the already existing chart DVRs, (iii) pole-free functions constant and proper ordered-map image for the registered algebraic/analytic comparison. No alternate Jacobian, arithmetic chosen centre regularity, global base-change completion, or formal height theorem follows merely from the companion source.
