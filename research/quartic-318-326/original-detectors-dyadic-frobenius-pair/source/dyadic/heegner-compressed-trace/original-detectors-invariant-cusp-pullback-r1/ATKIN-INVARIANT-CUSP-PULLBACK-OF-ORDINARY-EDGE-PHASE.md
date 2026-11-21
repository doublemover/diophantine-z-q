# An exact cusp-only Atkin-invariant pullback of the ordinary binary edge phase

The previously verified binary Heegner phase is a function of a matched ordinary 3-edge in characteristic two. This note realizes that same phase, after summation on a Frobenius-stable packet, by a characteristic-zero modular function on \(X_0(6)\). The stronger function is invariant under both \(w_2\) and \(w_3\), and has poles only at cusps. There is no evaluation on either original detector arm, no assertion of a holomorphic theta lift modulo \(2\), and no rank conclusion here.

## 1. Exact modular coordinates and the canonical branch

Use the cusp-normalized coordinates \(q=t_6,\ u=t_3\) of [Colò, Appendix A, Figure A.3](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf). Here \(q\) is a modular function, not the Fourier uniformizer. The two maps to \(X_0(3)\) and the level involutions are
\[
 u=\frac{q^2(q+9)}{(q+8)^2},\qquad u'=\frac{q(q+9)^2}{q+8},\qquad
 w_2q=-\frac{8(q+9)}{q+8},\qquad
 w_3q=-\frac{9(q+8)}{q+9}.
\]
The formula for \(u'\) also follows by composing the first map with \(w_2\); \(w_3u=729/u\) on the tame curve follows in the same way by substituting \(w_3q\). At an ordinary integral CM point use the branch \(q\equiv u-1\bmod 2\) of the first map. The second map there is the canonical connected 2-quotient, hence arithmetic Frobenius \(F\) on the tame coordinate at the unramified lift, including its transported cyclic 3-subgroup. This is the branch and normalizing convention in the [previous ordinary edge result](../original-detectors-chi17-dyadic-as-edge-phase-r1/FIRST-DYADIC-HEEGNER-BIT-IS-AN-ORDINARY-EDGE-MOMENT.md). At the ordinary finite points used here both \(u\) and \(u-1\) are units: \(u=0\) is a cusp of the forgetful \(j\)-map, and \(u=1\) reduces to supersingular \(j=0\).

Put
\[
 J=\frac{q^2-72}{q+8},\quad A=q+9,\quad S=A+\frac{9}{A},\quad
 Y=J+9=\frac{q(q+9)}{q+8},\quad
 J_*=\frac{S^2-36}{S-10}=Y+\frac{81}{Y}+18,\qquad
 T=\frac{(u+27)^2}{u}.
\]
Substitution verifies \(w_2J=J\), \(w_3Y=81/Y\); consequently \(J_*\) is invariant under both involutions. The poles of \(J\) belong to \(q=-8,\infty\); the poles of \(J_*\) belong to \(q=0,-8,-9,\infty\), the four cusps (also apparent from the forgetful map and its \(w_2\) conjugate). The surface of these identities is just the rational function field; no unresolved root choice is being made for \(J\) or \(J_*\). In the second coordinate,
\[
 T=\frac{(S+6)^3}{(S-10)^2},\qquad F(T)=\frac{(S-6)^3}{S-10}.
\]
Indeed \(u=(A-9)^2 A/(A-1)^2\), \(u'=A^2(A-9)/(A-1)\), while \(u+27=(A+3)^3/(A-1)^2\), \(u'+27=(A-3)^3/(A-1)\). Also \(T\equiv u^{-1}(u-1)^2\pmod2\), so with \(z=(u-1)^{-1}\) the binary phase \(T^{-5}\) is \((z^2+z)^5\), the Artin–Schreier equivalent of \(z^9+z^3\) already used in the one-bit result.

## 2. Exact fixed polynomials

Read coefficient vectors in ascending degree. The \(w_2\)-only polynomial \(f_2\) has vector
\[
 (507392,416256,540320,688976,666104,297649,678840,603080,0,1040318,911391).
\]
Writing \(\tau=u-1\), the exact identity modulo \(2^{20}\) is
\[
 f_2(J)=B_2(F(\tau))-B_2(\tau)+2^{19}(\tau^{-9}+\tau^{-3})
 \quad\text{in }(\mathbf Z/2^{20})[\tau,\tau^{-1}].
\]
The fully invariant polynomial \(f_*\) has vector
\[
 (24790720,8290800,10177780,11909401,14213408,26202676,26851175).
\]
The exact identity modulo \(2^{25}\) is
\[
 \Phi=f_*(J_*)=B_*(F(T))-B_*(T)+2^{24}T^{-5}
 \quad\text{in }(\mathbf Z/2^{25})[T,T^{-1}],
\]
where an explicit representative of \(B_*(T)\) is
\[
 4194304T^{-2}+18481152T^{-1}+26593280T+7859776T^2+26851175T^3 .
\]
The attached standard-library replay verifies both fixed polynomials and emits all Laurent coefficients, including \(B_2\). To explain the inverse branch used in that replay, each rational first map has the form \(x+E(x)\) with \(E\) reducing to zero on the Laurent chart. Substitute \(x\gets y-E(x)\) starting at the residual solution: the difference between successive inputs gains one power of 2, as Laurent denominators are units on this chart. Modulo \(2^K\) every inverse is the finite geometric series after removing its unique odd monomial. In passing from \(f(J)-2^{K-1}\mathrm{phase}\) to the displayed coboundary, the replay successively removes the lowest nonzero binary digit: an even exponent \(2e\) reduces to \(e\) modulo the image of \(F-1\) over \(\mathbf F_2\). It asserts the odd-chain remainder zero at every digit (including the constant term), then directly verifies the resulting Laurent identity at the full precision. No coefficient selection or comparison by point sampling is used.

## 3. Single-packet and cusp-expansion consequences

Let \(\mathcal A\) be a finite packet of the actual canonical lifts on the fixed tame orientation, closed under \(F\) with multiplicity. It can also carry an integer weight constant under \(F\). With this convention the sum of \(\Phi\) is divisible by \(2^{24}\); after division its reduction is exactly
\[
 \frac{1}{2^{24}}\sum_{a\in\mathcal A}\Phi(a)
   \equiv\sum_{a\in\mathcal A}\overline{T(a)}^{-5}\pmod2
\]
(with both sums weighted if applicable). The cancellation is before division. In particular this applies to the ordinary Frobenius-stable genus half in the earlier bit receiver, without additional dyadic digits or access to a second orientation. It supplies a characteristic-zero invariant function to which a modular trace lift could be applied; a lift with the normalization, all cusp conditions and arithmetic missing here is not inferred.

There is a useful independent Fourier principal-part cancellation. Let \(Q\) be the Fourier parameter at the width-one cusp \(\infty\). The canonical \(F\) branch at the Tate curve sends \(Q\mapsto Q^2\); \(T(Q)=Q^{-1}+O(1)\) has integral expansion and \(T(Q)^{-5}=O(Q^5)\). The second Laurent identity therefore gives, in the ordinary Laurent \(Q\)-expansion, that the constant coefficient of \(\Phi\) is divisible by \(2^{25}\), and
\[
 [Q^{-j}]\Phi \equiv [Q^{-j}]B_*(T(Q^2))-[Q^{-j}]B_*(T(Q))
       \pmod {2^{25}}\qquad(j>0).
\]
For any positive odd \(r\) and Dirichlet character \(\chi\) with \(\chi(2)=1\), it follows that
\[
 \sum_{j>0}\chi(j)[Q^{-rj}]\Phi\equiv0\pmod{2^{25}}
\]
in the integer ring of its values at 2. The change of variable \(j\mapsto2j\) identifies the two finite sums exactly. Full Atkin invariance makes the four normalized source-cusp expansions identical after transport by their Atkin matrices; individual vector-valued theta-cusp transport and integrality of a divided modular form still require a separate proof. Subtraction of the exact common constant does not change any binary packet value. These statements do not assert an evaluated production moment or a theorem on prime-index nonvanishing.

