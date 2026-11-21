# The next detector saturation sign is an oriented CM intersection ideal

The raw level-48 trace on either balanced selected detector twist is a rational fourth multiple, as in the preceding exact result. This note identifies the **next**, not the first, marking comparison. Its noncuspidal support lies on actual CM points of discriminant \(-192\), and its two residue signs can in principle be recovered from one relative fractional ideal. The signed ideal has not been computed on any original detector.

## 1. Fixed torsion direction and its exact noncuspidal CM fibre

Retain \(n\equiv23\bmod24\), \(D=-n\), \(K=\mathbf Q(\sqrt D)\), the full level-48 orbit \(x_{\mathfrak a}\), the raw map \(\phi\), and \(P=\sum_{\mathfrak a}\phi(x_{\mathfrak a})\) from the preceding fourth-divisibility result. In particular the fresh \(q_0\) is \(7\bmod24\), and each genuine \(p_\beta\ne17\) is \(1\bmod24\) in the actual linear-\(q\) support. These properties refer to the exact two Selmer-eight selectors, not an arbitrary Ready twist. Put \(P_{\mathfrak a}=\phi(x_{\mathfrak a})\) and \(J(Q)=T_3-Q\) on \(E_0:y^2=x(x+1)(x-3)\).

Over \(k_0=\mathbf Q(\sqrt3)\) take
\[
 T=(a,2a),\qquad a=3+2\sqrt3,\qquad m=2+\sqrt3 .
\]
Then \(2T=T_3\). For instance the line \(y=m(x-3)\) has factorization
\[
 y^2-x(x+1)(x-3)=-(x-3)(x-a)^2
\]
after substitution, so it is the tangent at \(T\) through \(T_3\). The four halves of \(T_3\) are precisely \(x=3\pm2\sqrt3,\ t=y/x=\pm2\). Under the literal \(X_0(48)\) map \(t=X-1/X,\ x=(Y+X^4+1)/(2X^2)\), their eight preimages are
\[
 X=t/2\pm\sqrt2,\qquad Y=\pm4\sqrt3\,X^2
\]
with the \(Y\)-sign prescribed by the sign of \(x-3\).

Use \(\pi_1^*t_{16}=X-2+3X/y_{48}\) and the forgetful tower in [Colò, Appendix A, pp. 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf):
\(t_8=t_{16}^2/(t_{16}+2),\
t_4=t_8^2/(t_8+4),\
t_2=t_4^2/(t_4+16),\
j=(t_2+256)^3/t_2^2\).
On the eight points the four \(j\)-values are distinct and each occurs twice. Their polynomial is
\[
 \begin{split}
 H_{-192}(u)={}&u^4-8041801037378436000u^3
 +15705521635909735050750000u^2\\
 &+826335556188178615474500000000u
 -1080060886113159937649308593750000 .
 \end{split}
\]
Here the label really is the order discriminant. In the 2-isogeny tower, source and quotient \(j\) on \(X_0(2)\) are \((z+256)^3/z^2\) and \((z+16)^3/z\). Starting from \(j=0\), the unique isomorphism class at the next lower order is \(54000\), discriminant \(-12\). Subsequent non-backtracking steps have discriminants \(-48,-192\): 2 is inert in \(\mathbf Q(\sqrt{-3})\), and at conductor divisible by 2 there is one ascending and two descending subgroups of order two. This follows also from the index-two lattices: the unique superlattice stable under the previous order is the ascending one; the other two lower the order by another factor two. At \(54000\), remove the one ascending edge to \(j=0\) in the resultant to get \(u^2-2835810000u+6549518250000\). At the two conductor-four nodes remove the two ascending edges to \(54000\), leaving the displayed \(H_{-192}\). The finite replay checks the rational tower on all eight points and verifies both resultant polynomial identities (interpolation at enough integer values for their respective degrees). Thus the fixed noncuspidal fibre consists of actual CM source elliptic curves of conductor eight in \(\mathbf Q(\sqrt{-3})\), not merely \(j\)-values of small height. No Heegner hypothesis at 2 for this fixed CM fibre is asserted.

The literal CM orbit is disjoint from this fixed fibre in characteristic zero, since its CM field \(K\) is different. This also gives a very useful good-prime separation. At \(q_0\) and each genuine \(p_\beta\), \(p\equiv1\bmod3\), so the fixed CM points reduce to ordinary curves, whereas the original CM points with \(p\mid D\) reduce to supersingular curves by the CM reduction criterion. All \(p\) here are greater than 3. Neither the source nor the fixed CM sections can reduce to cusps at these primes: their \(j\)-values are integral while the forgetful \(j\) has a pole at every cusp. No comparison at \(17\) follows from this argument.

## 2. A normalized fourth-root product and the next marking test

Define rational functions over \(k_0\),
\[
 h_T(Q)=\frac{y(Q)}{x(Q)-3}-m,\qquad
 f_T=h_T^2(x-3)=x(x+1)-2my+m^2(x-3).
\]
The tangent gives \(\operatorname{div}(h_T)=2(T)-(O)-(T_3)\) and \(\operatorname{div}(f_T)=4(T)-4(O)\). Direct coordinates for \(J\) give
\[
 h_T(JQ)=h_T(Q),\qquad (x(JQ)-3)(x(Q)-3)=12,\qquad
 f_T(Q)f_T(JQ)=12h_T(Q)^4. \tag{1}
\]
Here \(f_T(T_3)=12\). Thus the input functions \(h_T(P_{\mathfrak a}),f_T(P_{\mathfrak a})\) are finite and nonzero in characteristic zero and units at the comparison primes of §1. Their preimages of \(O,T_3\) are cusps by the exact level geometry and the Fricke identity.

Let \(\lambda:E_0\to E'=E_0/\langle T\rangle\) be the cyclic degree-four quotient and \(\widehat\lambda\) its dual, so \(\widehat\lambda\lambda=[4]\). Write \(\mu=\ker\widehat\lambda\); it is rational over \(k_0(i)\) by Cartier duality with the constant order-four kernel of \(\lambda\). On \(E'\) choose \(R_4\) with divisor \(\widehat\lambda^*((T)-(O))\). This divisor is principal: pullback on elliptic \(\operatorname{Pic}^0\) is \(\lambda\), which kills \(T\). It is rational over \(k_0\), so a function exists over \(k_0\) (Riemann–Roch descends in this principal degree-zero case). Normalize at \(O\) by \((z\circ\widehat\lambda)R_4\to1\) for \(z=-x/y\) on \(E_0\). The leading coefficient of \(f_T\) is one in \(z^{-4}\), so \(R_4^4=f_T\circ\widehat\lambda\) exactly.

Translation \(B\mapsto B+k\) by \(k\in\mu\) changes \(R_4\) by a character \(\xi(k)\in\mu_4\). It is faithful: if its image had exponent at most two, \(R_4^2\) would descend to a function with divisor \(2(T)-2(O)\), contradicting \(2T=T_3\ne O\). The same argument in residue characteristics \(p>3\) applies to the good, étale isogeny models, since the order of \(T\) is preserved and the normalized function has the same divisor. In particular the character on special fibres is the reduction of the one global character. One can see the normalization directly on these models: the rational function has the indicated horizontal divisor, and its leading coefficient 1 at the étale formal origin rules out any vertical order on the good model's integral fibre. On the preimage of any base unit locus, \(R_4\) and its inverse are regular by the equation and normality.

Choose arbitrary lifts \(A_{\mathfrak a}\) of \(P_{\mathfrak a}\), \(A=\sum A_{\mathfrak a}\), and \(C_4=\prod R_4(A_{\mathfrak a})\). By the preceding proof \(P\) is a fourth multiple of a point of \(E_0(K)\), including the zero case. Hence all possible lifts of \(P\) to \(E'\) are rational over \(K(i,\sqrt3)\). For a Galois automorphism over that field, the index permutation changes the selected lifts by kernel elements with sum zero (the sum \(A\) is fixed). Their characters multiply to one, proving \(C_4\in K(i,\sqrt3)\).

Let \(\chi=\chi_{17}\) from the rational-double result, and form the same genus-half product at **both** comparison primes:
\[
 M=\prod_{\chi(\mathfrak a)=+1}h_T(P_{\mathfrak a})\in K(\sqrt{17},\sqrt3),
 \qquad U_4=\frac{C_4}{12^{h/8}M}\in L=K(i,\sqrt3,\sqrt{17}). \tag{2}
\]
Here \(16\mid h\): use independent ramified ideal classes at 17 and any three genuine primes, by the same nonsquare norm \(<n/4\) argument as before. Complex conjugation of the full orbit sends indices by the level-inverse involution, which has \(\chi\) sign \(-1\). Since \(J\) fixes \(h_T\), \(\bar M\) is the product on the other half. Consequently by (1)
\[
 (C_4\bar C_4)^4=12^h(M\bar M)^4.
\]
The two real numbers \(C_4\bar C_4\) and \(12^{h/4}M\bar M\) are positive in the chosen complex embedding. This gives \(U_4\bar U_4=1\) for the ordinary complex conjugation \(c\) of the CM field \(L\).

At either \(q_0\) or \(p_\beta\), reduce in a field containing all chosen lifts. For any reference lift \(S\) of \(T_3\), (1) shows that the fourth power of
\[
 \frac{R_4(S-B)R_4(B)}{h_T(\widehat\lambda B)}
\]
is 12; thus this quotient is a constant. As \(B\to O\), \(R_4(B)\sim (z\circ\widehat\lambda)^{-1}\), \(h_T(\widehat\lambda B)\sim-(z\circ\widehat\lambda)^{-1}\), and \(R_4(S)^4=12\). The constant is exactly \(-R_4(S)\), not an undetermined root of unity. This calculation holds in the residue field too. Each inertia pair has lift sum \(S+k\); its root-product divided by its \(h_T\)-value is \(-R_4(S)\xi(k)\). Pairs exchange the two \(\chi\) halves, so multiplying the denominators uses \(M\) exactly once. There are \(h/2\) pairs, divisible by eight, and \(8S=O\) because \(2S\in\mu\). Thus
\[
 \widetilde A=\sum k,\qquad \widetilde U_4=\xi(\widetilde A).\tag{3}
\]
Here tildes denote reductions at a chosen place, not complex conjugation. This is independent of the arbitrary reference \(S\). In comparing at two rational primes, interpret the residue value by the reduction of the same fixed abstract \(\mu_4\subset L\), rather than independently choosing a root of \(-1\) at each prime. This is important at \(q_0\equiv7\bmod24\), where \(i,\sqrt3\) need not be in the rational residue field.

Take a rational quarter \(B_D\) of \(P_D\), and its twist image \(B\in E_0(K)\). At a comparison prime \(\widetilde{2B}\in E_0[2]\) because \(\widetilde P=O\). In fact \(\widetilde{2B}=O\): subtract the descended rational torsion point given by this reduction, and the remaining formal anti-invariant point gives even Kummer parities by the prior formal-parameter calculation. But \(2B_D\) has zero Kummer class and the torsion parities are injective, so that torsion point was zero. Therefore \(\widetilde B\in E_0[2]\). The character \(\xi(\lambda(\widetilde B))\) is \(+1\) on \(O,T_3\) and \(-1\) on the other two 2-torsion points, by the kernel \(\langle T\rangle\). This is precisely the sign of the first Kummer valuation parity of \(B_D\): subtract its rational torsion reduction as above, and only the torsion point contributes the first parity. The two lifts \(A,\lambda(B)\) differ by one global element of \(\mu\). Thus the two values in (3) differ exactly when the first parities of \(B_D\) differ. In the actual balanced Selmer basis this difference is its mark coefficient. In the zero case \(B_D\) is torsion, so the two signs agree.

In particular opposite residues in (3) certify that the **quarter** has a nonzero mark component, after which a rational 2-torsion correction gives the actual mark; they also certify \(P_D\ne O\), hence its nontorsion and rank one from the actual Selmer eight. Equal residues only show that \(P_D\) is an eighth multiple (subtract torsion from \(B_D\), then multiply by four); they do not imply rank zero. No residue from (3) has been evaluated for an actual detector.

## 3. What relative ideal computation is left

The coherent residue comparison in (3) is determined by the fractional ideal \((U_4)\) **together with the norm-one condition**, not by the class number alone. Indeed any two generators of that ideal with norm one to \(L^c\) differ by a root of unity: a norm-one unit in a CM field has modulus one in all embeddings. A common root of unity does not change equality of the residue phases, since reduction on the relevant roots of unity is injective at these comparison primes. Here \(L\) is multiquadratic, so its roots of unity have order dividing 24; all comparison primes are prime to 6. This provides a possible compact certificate: give the exact oriented ideal in \(L\), a certified norm-one generator, and compare its residue roots of unity under the two reductions. The proof does not claim one can obtain the ideal from the ordinary class polynomial without orientation.

For \(p>3\) the ideal is a signed CM–CM intersection calculation. Use a common absolute normalized valuation at a place of all points and \(\sqrt3\) (or use ordinary integral intersection multiplicities and scale by ramification). Let \(I_{\mathfrak a}\) be the normalized intersection multiplicity of the section \(P_{\mathfrak a}\) with \(T\) on the good model of \(E_0\). It is zero off an actual collision in the fixed **marked fibre** of §1. Since \(O,T_3\) have only cuspidal preimages, no point in the orbit reduces to either at \(p>3\). The horizontal divisors therefore give
\[
 v(h_T(P_{\mathfrak a}))=2I_{\mathfrak a},\qquad
 v(f_T(P_{\mathfrak a}))=4I_{\mathfrak a}.
\]
There is no vertical contribution on the good model, from the unit leading coefficients at \(O\). Equation (2) now gives exactly
\[
 v(U_4)=\sum_{\chi=-1} I_{\mathfrak a}-\sum_{\chi=+1} I_{\mathfrak a}\qquad(p>3). \tag{4}
\]
To turn a normalized valuation \(v(p)=1\) into the exponent in the fractional ideal of \(L\), multiply by the ramification index of the corresponding place of \(L\).

The only possible good support consists of primes nonsplit in both \(K\) and \(\mathbf Q(\sqrt{-3})\): opposite ordinary/supersingular types cannot collide, and two ordinary reductions from different CM fields cannot be isomorphic (the ordinary endomorphism algebra has just one quadratic field). At \(p\mid n,\ p\ne17\), even a collision cancels in (4), since the free inertia involution fixes \(\sqrt3\), exchanges \(\chi\) halves and \(h_T\) is \(J\)-invariant. There is also automatic cancellation at primes inert in both fields with \(p\equiv11\bmod12\) and \((17/p)=+1\): their Frobenius in the unramified multiquadratic field \(L\) is ordinary complex conjugation, which then fixes the place, so \(U_4\bar U_4=1\) makes its valuation zero. These exclusions do not calculate the remaining signed intersections, or the bad-place exponents at 2 and 3. A norm of an unmarked \(j\)-difference would count a larger set of level flags and would lose the \(\chi\) sign. The required input is the **oriented**, genus-signed ideal of (4), with its two bad-place components, or the coherent residues themselves. No generic rank converse is being assumed.

### Exact replay and scope

The primary predecessor is *The first half of the raw level-48 detector trace is unmarked*, paper **bbfe4e889f688bcf69f8b643fc60615fb0945ff0ab1862ff21e28127744535f3**. Its own predecessor fixes the index/pair signs and the Selmer basis. The local conductor and comparison primes use the exact original balanced paired selector and its linear-\(q\) congruences, not a surrogate CM example.

The finite replay checks the \(-192\) fibre and the two degree-two resultants in exact arithmetic. It certifies no sign at a literal pole and no rational marked point.

    python3 -B replay_marked_cyclic_four_cm192.py | cmp - EXACT-MARKED-FIBRE-CM192.json
    sha256sum -c SHA256SUMS
