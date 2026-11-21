# Two exact trace entries on the original modular Jacobian

Fix the same level \(M=2^{28}3^6 S^2\), same selected monic root equation \(p\), and same modular \(J\) as in the original reverse-height argument. The compactification is the smooth projective \(X_1(M)\) obtained from the full original characteristic-zero ordinary chart. Put
\[
 A_0=\mathcal{O}_L[J],\quad K=L(J),\quad F=K[x]/(p_K),\quad
 B=\operatorname{Nor}_{F}(A_0).
\]
The field \(L\) is the already selected common field. Let \(H\) be the actual finite flat invariant lattice of the modular Jacobian \(J_X\) over \(\mathcal{O}_L\), not the lattice of the other abelian surface \(A\). The existing generic Abel–Jacobi map sends \(h\) to \(\omega_h\); write \(\omega_h=c(h)\,dJ\) in the same field \(F\).

## A whole forced column

For every \(h\in H\),
\[
 \operatorname{Tr}_{F/K}(c(h)\cdot 1)=0.
\]
In particular, \(t_{i,1}=0\) is an exact integer polynomial witness for every row of any genuine finite generating family, where the normalization generator list is enlarged by \(1\in B\).

For the finite morphism of smooth characteristic-zero curves \(J:X_1(M)_L\to\mathbb P^1_L\), the map on rational differentials is the \(K\)-linear scalar trace in the fixed \(dJ\) frame. It takes regular differentials to regular differentials. To see this directly, complete at any closed base point and pass to a separable extension splitting the residue branches. For each branch choose uniformizers with \(t=z^e\), absorbing a unit with an \(e\)-th root in characteristic zero. For \(\sum_{m\ge0}a_mz^m\,dz\), the \(dt\) coefficient is \(\frac1e\sum_{m\ge0}a_m z^{m+1-e}\). The field trace on that completed branch kills every exponent not divisible by \(e\); every surviving exponent, as a \(t\)-power, is nonnegative. Summing the branch traces gives the completed base trace, and integrality descends along the faithful residue extension. Equivalently one may use [finite duality and its trace](https://stacks.math.columbia.edu/tag/0FKW).

Thus the base \(dJ\) coefficient lies in \(L[J]\), and the \(d(J^{-1})\) coefficient, its negative times \(J^2\), lies in \(L[J^{-1}]\). The only polynomial \(f(J)\) with \(-J^2 f(J)\in L[J^{-1}]\) is zero: the latter expression is in both polynomial rings, so is constant, and it vanishes at \(J=0\). This proves the same zero that the finite monic remainder evaluator returns. It is not a vanishing of the entire trace matrix.

## A genuinely nonzero row and an exact nonzero entry

Since \(32\mid M\), the map
\[
 \pi:X_1(M)\longrightarrow X_0(32),\qquad
 (E,P)\longmapsto(E,\langle (M/32)P\rangle)
\]
is defined over \(\mathbb Q\), nonconstant, extends to the proper curves, and is given by the identity on the upper-half-plane parameter. The marked point has exact order \(M\), so the displayed subgroup has exact order \(32\). The map is unchanged under \(P\mapsto-P\).

[Tian, Proposition 2.1](https://archive.ymsc.tsinghua.edu.cn/pacm_download/232/8762-35_Ye_Tian_Congruent_Numbers_and_Heegner_Points.pdf#page=6) identifies the actual \(X_0(32)\) over \(\mathbb Q\) with \(Y^2=X^3+4X\), taking the infinity cusp to the origin. Its invariant \(dX/(2Y)\) gives a nonzero rational form. One may use the normalization \(f_{32}\,dq/q\), where \(f_{32}=\eta(4\tau)^2\eta(8\tau)^2=q+O(q^5)\), as in [Wen-Ching Winnie Li, Ling Long and Fang-Ting Tu, §3.1 and (3.1)](https://sigma-journal.com/2018/090/sigma18-090.pdf#page=15). The latter gives \(dx/y^3=4f_{32}\,dq/q\) on \(x^2+y^4=1\). The normalized form is rational by its rational \(q\)-expansion at the rational cusp. Any nonzero rational multiple gives a certificate.

Pull back \(f_{32}\,dq/q\) along \(\pi\) and denote the result by \(\omega\). It is nonzero by separability. Its literal \(dJ\) coefficient has expansion
\[
 a_\omega=\frac{f_{32}(q)}{q\,dJ/dq}=-q^2+O(q^4).
\]
Infinity has width one for \(\Gamma_1(M)\), so \(q=e^{2\pi i\tau}\) is unchanged and \(J=q^{-1}+744+O(q)\). The inverse image of \(\omega\) under generic Abel–Jacobi lies in \(L\otimes H\). Clear its denominators with one nonzero \(r\in\mathcal{O}_L\); then \(r\omega=\omega_h\) for a genuine nonzero \(h\in H\). Append \(h\) to any finite global generating family of \(H\).

Put \(a=c(h)\ne0\). Choose a genuine nonzero polynomial \(s\in A_0\) such that \(b=s/a\in B\), by clearing the denominators of an integral equation for \(a^{-1}\). For instance, if the monic minimal equation of \(a^{-1}\) over \(K\) has coefficients \(u_i\) and \(s u_i\in A_0\) for every \(i\), the equation of the scaled root \(s a^{-1}\) has coefficients \(s^{d-i}u_i\in A_0\). Thus \(b\) is an actual normalization element. Append it to any finite normalization generators. Its row entry is exactly
\[
 \operatorname{Tr}_{F/K}(a b)=[F:K]\,s,\qquad [F:K]=\deg p;
\]
this is a nonzero polynomial in \(A_0\), not a demonstration on a smaller field. The finite monic remainder formula checks the same witness once the two representatives in \(p_K\) are supplied. These entries coexist in one genuine finite certificate by the earlier global-matrix equivalence and the actual same-lattice geometric trace theorem. They do not numerically enumerate the rest of its matrix.

## Formal boundary

The staged small arithmetic theorems derive the two-chart vanishing and the nonzero normalization multiplier. Their actual consumer takes the same original chart and global coefficient map. The compact forgetful map, the actual integral Abel–Jacobi comparison, and the regular differential pushforward in the first argument are classical geometry, not newly checked Lean. The code does not use a mock kernel or replace \(X_1(M)\) with \(X_0(32)\); the latter supplies a nonzero differential only.
