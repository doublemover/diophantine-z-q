# An exact CM-supported replacement for the inert-29 cubic readout

A fixed modular function with only CM and cuspidal horizontal divisors reproduces the cubic phase at every one of the 224 geometric supersingular ordered level-48 flags. This is a proved alternative arithmetic input for the original selected targets, not an evaluation of a moving conductor or a new rational point.

## 1. A symmetric principal Hecke divisor

Use the same short model \(C=X_0(48): Y^2=X^8+14X^4+1\) and modular cusp \(\infty\), with \(X=q^{-1}+\cdots\) and \(Y/X^4\to+1\) at the Tate branch. See [Colò, Appendix A, pp. 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf). Set
\[
 b_0=1,\qquad b_1=Y+X^4,\qquad b_{k+1}=X^k(Y+X^4+7)\quad(1\le k\le4).
\]
At the other infinity \(Y=-(X^4+7-24X^{-4}+\cdots)\), the six functions have no pole. They are regular on the affine chart and have distinct Tate-cusp orders \(0,-4,-5,-6,-7,-8\); every nonconstant leading coefficient is 2. Riemann–Roch makes them a basis for \(H^0(C,\mathcal O(8\infty))\) in characteristic zero or at 29.

The literal symmetric function is
\[
\begin{aligned}
 \mathcal G(P,Q)={}&2+2b_5(P)+2b_5(Q)-2b_1(P)b_1(Q)\\
                 &-b_2(P)b_4(Q)-b_4(P)b_2(Q)+2b_3(P)b_3(Q).
\end{aligned}
\]
Its divisor is exactly \(T_5+2\Delta-8(\{\infty\}\times C)-8(C\times\{\infty\})\), where \(T_5\) is the reduced cyclic 5-isogeny correspondence and \(\Delta\) the diagonal.

For context the relation comes from \(T_5=-2\) on \(J_0(48)\). The genus is three. The level-24 newform \(g=\eta_2\eta_4\eta_6\eta_{12}\) contributes two independent old forms \(g(z),g(2z)\); the level-48 newform is the quadratic twist of \(g\) by \(-1\) (see [Feng–Liu–Pan–Tian, §2.1](https://arxiv.org/pdf/2405.11132)). The coefficient of \(q^5\) in \(g\) is \(-2\) and is unchanged by twisting. The good-prime Hecke operator acts by these scalars on the three differentials, and a zero-differential endomorphism over characteristic zero is zero. The explicit computation below proves the divisor identity independently, without relying on any unspecified seesaw constant or descent.

For that computation use the literal eta quotient \(X=\eta_4\eta_{16}^2\eta_{24}^3/(\eta_8^3\eta_{12}\eta_{48}^2)\), with \(Y\) the indicated branch of the square root. The replay checks every coefficient from \(q^{-48}\) through \(q^{114}\) in both \(\mathcal G(P(q),P(q^5))\) and \(\mathcal G(P(q),P(q))\). The first is the pullback to \(X_0(240)\), of possible polar degree at most \(8(6+6)=96\) because its two projections both have degree six. Its only possible local negative powers at this Tate cusp start at \(-48\). The integral Laurent zero test beyond the total polar degree proves exact vanishing on the whole irreducible correspondence. Generically the map onto \(T_5\) has degree one: a pair of cyclic 5-isogenies from the generic no-extra-endomorphism elliptic curve to isomorphic targets would give a dual composition of norm 25, hence \(\pm[5]\), which forces equality of the kernels. Thus \(T_5\) has bidegree \((6,6)\). The diagonal test exceeds its polar degree 16, and symmetry forces its vanishing order to be even (swapping factors negates the conormal). The diagonal is not a component of \(T_5\). These two zero components exhaust both polar degree budgets of 8; an additional effective curve has positive degree against at least one generic projection fiber. This proves both the claimed multiplicities and the absence of lost poles or cusp factors. The same argument works after reduction at 29: the good characteristic differs from 2, 3 and 5, the basis remains independent, the tame modular curves and cusp expansions specialize, and the Laurent identities are integral.

For a noncuspidal CM flag \(P\), the zeros of \(\mathcal G(P,Q)\) in \(Q\) are the actual CM flag and its cyclic 5-neighbors with their multiplicities. All poles are cuspidal. A flag \(P\) reducing ordinary at 29, and each of these prime-to-29 neighbors, stays ordinary. Consequently the specialization is a unit at every supersingular flag in the chosen reduction. This is not the non-CM-supported characteristic-zero lift of a cubic Tate tangent.

## 2. An exact nine-row certificate

Use \(k=\mathbf F_{29}[s]/(s^2-2)\), \(\gamma=14+5s\in\mu_3\), and let \(F\) denote 29-Frobenius. For a fixed ordered supersingular flag \(Q\), let \(\kappa(Q)\in\mathbf F_3\) be the exponent of \([4](1-F)\bar\phi(Q)\) modulo 3 in the coherent order-nine generator \(G=(14,13s)\). This is the exact previous Tate receiver. For \(A=(1,w_{16},w_3,w_{48})\) put \(\epsilon_A=(1,1,-1,-1)\). Define \(v_P(Q)\) by \(\mathcal G(P,Q)^{560}=\gamma^{v_P(Q)}\), and put
\[
 v_P^*(Q)=\sum_A\epsilon_A\big(v_P(AQ)+v_{FP}(AQ)\big).
\]
The paired sum implements Frobenius anti-projection because \(v_{FP}(Q)=-v_P(FQ)\). The signs are those of the actual Atkin phase identities. The normalization is exactly as printed, with no unmentioned divide-by-two or divide-by-eight.

Represent \(a+bs\) by \(a+29b\). The nine ordinary rows \((X,Y,c)\) are
\[
 (65,660,1),\ (147,317,-1),\ (159,256,-1),\ (191,789,-1),\ (192,723,1),\
 (253,274,1),\ (324,526,-1),\ (367,497,1),\ (393,327,1).
\]
For **every one** of the 224 fixed ordered supersingular labels the exact identity is
\[
                          \kappa(Q)=\sum_i c_i\, v_{P_i}^*(Q).
\]
The replay independently enumerates the full supersingular label set, recomputes the elliptic phase, checks all required \(\mathcal G\) values are nonzero, and verifies this finite identity entry by entry. There are 672 ordinary noncuspidal \(k\)-points, none \(\mathbf F_{29}\)-rational; the projected vectors from one point of each of their 336 Frobenius pairs have rank 25. The nine inputs are not claimed minimal.

## 3. Algebraic lifts and the remaining relative arithmetic

For each chosen ordinary flag lift the ordinary elliptic curve canonically (with all endomorphisms) over \(W(k)\) and lift its cyclic prime-to-29 subgroup by étaleness. Canonical lifts have CM, hence algebraic modular coordinates; the modular point lies in the unramified degree-two 29-adic field at the specified place. For the canonical lift characterized by lifting endomorphisms, see [*On the p-adic geometry of traces of singular moduli*, Proposition 3](https://arxiv.org/abs/math/0502213); see also [Erdoğan’s Witt-coordinate result, Theorem 4.1](https://arxiv.org/abs/1211.1152). Take, inside this local field, the number field generated by all nine sets of lifted coordinates and their local Frobenius conjugates. It is stable under this involution; its fixed subfield \(F_0\) embeds at the chosen place into \(\mathbf Q_{29}\). No global total-reality or CM assumption on \(F_0\) is made.

Write \(\widetilde P_i,\widetilde P_i^\sigma\) for the two chosen lifts and set
\[
 \mathcal U(Q)=\prod_{i,A}\!
   \left(\mathcal G(\widetilde P_i,AQ)\,
         \mathcal G(\widetilde P_i^\sigma,AQ)\right)^{c_i\epsilon_A}
   \quad\in F_0(C)^\times .
\]
The \(A\) maps are rational and preserve CM and cusps. Thus all horizontal divisors of \(\mathcal U\) are CM or cuspidal. It is a unit at the named reductions and satisfies \(\overline{\mathcal U}(Q)^{560}=\gamma^{\kappa(Q)}\) on the entire fixed chart.

For the same actual primitive genus character on either odd arm, divide the two oriented genus-half products of \(\mathcal U(Q_\alpha)\), preserving every CM index and its multiplicity. These are the two norms after base change to \(F_0\), interpreted in a finite étale tensor algebra if the coefficient field and ring class fields intersect. Thus the arithmetic recipe never accidentally substitutes a smaller compositum Galois orbit. At the named prime above 29 its exponent 560 gives precisely the full signed order-nine phase modulo 3. A noncube certifies exact order nine and the corresponding rational marked side by the existing torsion/Selmer argument. A cube does not exclude order three or a rational point. The replay evaluates no such norm on a moving discriminant or conductor.

CM support is now exact. A usable evaluation theorem would still have to preserve the two genus cosets, the ordered level-48 flags, and the oriented **unit** at the chosen prime above 29. [Ehlen, *Singular moduli of higher level*, Theorem 6.4 and §5](https://arxiv.org/pdf/1505.02711) uses square-free level and explicitly oriented Heegner-divisor input; as stated it does not compute this level-48 relative norm on the moving ring-class family. An absolute norm, or an ideal factorization without controlling units over \(F_0\), is not the needed value. No such evaluation or compressed runtime is asserted here.

~~~sh
sha256sum -c SHA256SUMS
python3 -B verify_CM_supported_cubic.py | cmp - EXACT-CM-SUPPORTED-CUBIC.json
~~~
