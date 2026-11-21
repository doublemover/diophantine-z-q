# The fixed original Kummer fibre has no rational formula even in the full shift chart

This concerns the **fixed second parameter** \(t'=1/c\) and actual scalar input \(a=0,h=473592745039516333133760\) of [the selected original raw fibre](../ct-original-scalar-kummer-fiber-r1/ACTUAL-RAW-POINTPAIR-KUMMER-AND-SCALAR-FIBER.md). It rules out a rational-function construction in the full shifted point after keeping the actual unshifted input fixed. It does **not** rule out an arithmetic rational point at the actual shifted point, a formula on a special lower-dimensional locus, a varying second parameter on the Kummer surface, or an argument varying the original \(h\).

## 1. Family retaining the actual curve, shift norm and all shift coordinates

Write \(K=\mathbf Q(\sqrt2)\), put \(d=3-\sqrt2\), and keep the exact source
\[
 E/K:y^2=x(x^2-d^2),\qquad
 P_0=(1+\sqrt2,2\sqrt2),\qquad
 U(P)=\frac{2y(P)}{x(P)^2+d^2}.
\]
Fix the source \(R=4376874610839020\), \(\beta=204618888056724185\), \(D_0=1+114444R\),
\[
 H=N_{K/\mathbf Q}(U([h]P_0)),\quad
 N=1+(H/R)^2+2\operatorname{Re}(U([h]P_0)^2)/R.
\]
The literal actual shifted point is \(P_*=[6^{15}3^{65536}J] P_0\) (same frozen J). With variable shifted point \(P\) on the Weil restriction \(X=\operatorname{Res}_{K/\mathbf Q} E\), use the **same** formula
\[
 q(P)=\frac{N_{K/\mathbf Q}(U(P))}{HR^{15}},\qquad
 c(P)=\frac{12(N^2+R q(P)^2)}{D_0},\qquad
 \lambda(P)=1+3\beta c(P)^2.
\]
At \(P=P_*\) these are the literal source values, not a replacement norm. The statement is that the smooth projective fibre
\[
 V^2=\lambda(P) f_\beta(t),\qquad f_\beta(t)=(t^2-\beta)(t^2+3\beta)
\]
has no \(\mathbf Q(X)\)-point. In geometric generic coordinates its only solutions are its four branch points. In particular, an identity in the shift norm alone or an identity retaining the coordinates of both conjugate shifted curve points is excluded on this family.

## 2. The trivializing curve and one exact place

Let \(G=432\beta\). The quadratic base change splitting this fibre is pulled back from the smooth projective double cover \(C\to\mathbf P^1_q\)
\[
 C:\quad s^2=D_0^2+G(N^2+Rq^2)^2.
\]
The even quartic coefficients \(a_4=GR^2,b_2=2GRN^2,c_0=D_0^2+GN^4\) satisfy
\[
 b_2^2-4a_4 c_0=-4GR^2D_0^2.
\]
Here \(a_4,c_0\) are nonzero, so the quartic is separable, of genus one, and unbranched over \(q=0,\infty\). Its Jacobian has
\[
 j_C=\frac{16 (b_2^2+12a_4c_0)^3}{a_4c_0(b_2^2-4a_4c_0)^2}.
\]
This follows directly from [Fisher's binary-quartic normalization, §2 (2)](https://people.maths.bris.ac.uk/~jb12407/ANTS-XV/papers/ANTS-XV_fisher.pdf), with \(I=b_2^2+12a_4c_0\), \(J=72a_4b_2c_0-2b_2^3\) and \(4I^3-J^2=432a_4c_0(b_2^2-4a_4c_0)^2\).

At \(p=181\), the verified actual chart has \(N\equiv120\) and \(v_{181}(D_0)=1\). Both \(G,R\) are units and \(b_2^2+12a_4c_0\equiv16G^2R^2N^4\ne0\). Therefore \(v_{181}(j_C)=-4\). The target constant quartic \(C_\beta:v^2=f_\beta(t)\) has Jacobian \(E'_\beta:Y^2=X(X^2-4\beta X+16\beta^2)\) with \(j=2048/3\), an 181-unit. They cannot be geometrically isogenous: potential good reduction is equivalent to integrality of j, and is preserved by isogeny after any finite field extension ([Silverman, *Arithmetic of Elliptic Curves*, VII.5.5, VII.7.2–3](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf)). Equally, the two conjugate source curves have j=1728, integral at 3, while the target does not. None of the three elliptic curves just listed is geometrically isogenous to the target.

Already, any rational formula just in q would give a morphism \(C\to C_\beta\) by \(v=D_0 V/s\); this would be constant. The next argument is needed to retain *all* shift coordinates, not just q.

## 3. Literal pencil and the three Albanese factors

Work over \(\overline{\mathbf Q}\). Now \(X=E_+\times E_-\) and \(q=U_+U_-/(HR^{15})\). On each elliptic curve the four zeros of U are its origin and the three points with \(y=0\). The four poles are the two points at each of \(x^2=-d_\pm^2\). All are simple and disjoint: at finite zeros use y as a parameter; at a pole x is a parameter; at the origin x,y have pole orders 2,3. Consequently the zero and pole divisors of the pencil are each in the same line bundle \(\mathcal A\) (the exterior product of degree-four bundles) and meet in exactly **32** transverse base points: the zero set in one factor crossed with the pole set in the other, in both orders. No common divisor. Blow up these points, \(\pi:S\to X\), and let \(F\) be a fibre divisor of the actual resolved q. Each exceptional divisor maps isomorphically to the projective q-line: near a base point the pencil is a unit times \(u/v\) for two independent local parameters. Thus
\[
 F=\pi^*\mathcal A-\sum E_i,\quad F^2=0,\quad K_S=\sum E_i,\quad K_S\cdot F=32.
\]
Additive notation denotes line bundle classes. In particular pullback of the degree-two branch line bundle on the q-line is \(\mathcal O_S(2F)\).

The fibre product \(T=S\times_{\mathbf P^1_q} C\) is a finite flat double cover with pushforward \(\mathcal O_S\oplus\mathcal O_S(-2F)\). Its only possible singularities are ordinary double points. To see this on the same curves, away from zeros/poles the only critical points of a product of unit functions \(U_+U_-\) are pairs of critical points of U. There the derivative numerator for U in the x-coordinate is
\[
 -x^4+6d_\pm^2x^2-d_\pm^4.
\]
Its four distinct roots are away from \(y=0\) and the chart poles, so each ramification of U is simple. In completed local parameters at a critical pair the normalized product is \((1+x_1^2)(1+x_2^2)\); subtract 1 and use \(x'_2=x_2\sqrt{1+x_1^2}\) to obtain \(x_1^2+(x'_2)^2\). A branched base change therefore produces an A1 singularity. The exceptional curves of S are sections, so points on them are not critical. Above 0 and infinity the change of base is étale, including all intersections of zero/zero or pole/pole. This proves the claim. The double cover is connected since \(H^0(S,\mathcal O_S(-2F))=0\): a nonzero section would make the negative of a nonzero effective fibre divisor effective as well on a projective integral surface. It is normal by the hypersurface local model and smoothness in codimension one. Resolving the A1 points does not change \(H^1(\mathcal O)\) (ordinary double points are rational singularities). Denote a smooth projective resolution by \(\widetilde T\).

We compute \(h^1(S,\mathcal O_S(-2F))=1\) directly, so there is no implicit assumption on the fibre Pryms. The base subscheme \(Z\) is a complete intersection of the two sections of \(\mathcal A\). For the Koszul sequence
\[
 0\longrightarrow \mathcal O_X\longrightarrow \mathcal A^{\oplus2}
   \longrightarrow \mathcal I_Z(2\mathcal A)\longrightarrow0,
\]
use \(h^0(\mathcal A)=16, h^1(\mathcal A)=0\) from degree four on each elliptic factor and Künneth; \(h^1(\mathcal O_X)=2\). Thus \(h^0(\mathcal I_Z(2\mathcal A))=32-1+2=33\). On S this is precisely \(h^0(K_S+2F)\) because \(K_S+2F=\pi^*(2\mathcal A)-\sum E_i\). By Serre duality \(h^2(\mathcal O_S(-2F))=33\); by Riemann–Roch \(\chi(\mathcal O_S(-2F))=\chi(\mathcal O_S)+(-2F)(-2F-K_S)/2=32\), since \(\chi(\mathcal O_S)=\chi(\mathcal O_X)=0\). With the vanishing of \(h^0\) this gives the claimed 1. Therefore \(h^1(\mathcal O_{\widetilde T})=2+1=3\).

The morphisms to \(E_+,E_-,C\) produce three independent pullbacks of regular differentials. The first two descend to X and are independent (the map to X is dominant); they are fixed by the covering involution. The nonzero differential from C is negated by the involution, because its quotient is \(\mathbf P^1\). This can be read on the common smooth dense open, without choices of equivariant resolution. By the Albanese universal property and the equality of tangent ranks, the induced map is an isogeny
\[
 \operatorname{Alb}(\widetilde T)\;\sim\;E_+\times E_-\times \operatorname{Jac}(C).
\]
Each factor was excluded at its explicit prime in §2. Any rational map \(\widetilde T\dashrightarrow C_\beta\) thus is constant: it extends to the smooth projective source ([Weil extension, Milne Theorem 3.1](https://jmilne.org/math/articles/1986b.pdf)) and its homomorphism out of the Albanese is zero.

A generic fibre point would induce such a constant map via \((t,v)=(t,D_0V/s)\), including the two possible quartic infinities. The involution \(s\mapsto-s\) sends v to −v, exchanging those two infinities; its only fixed points are the four finite roots of \(f_\beta\), with \(V=0\). Their parameters are not rational. Since X is geometrically integral, no algebraic constant outside \(\mathbf Q\) belongs to \(\mathbf Q(X)\). So no \(\mathbf Q(X)\)-point exists as claimed.

## 4. Relation to the literal shift and falsifiability

The integer multiples of the actual \(P_0\) in X are Zariski dense, not contained in a hidden isogeny graph. At the two verified inert good primes 181 and 1346909 the annihilators are respectively \(32724=324\cdot101\) and \(1814161575200\), which is prime to 101. At 181 the nonzero computed \([h]P_0\) has \(h\equiv5832=18\cdot324\pmod{32724}\), so \([324]P_0\ne O\) and 101 divides the exact reduction order. Good reduction is injective on prime-to-residue-characteristic torsion ([Silverman, VII.3.1](https://www.pdmi.ras.ru/~obenoist/refs/Silverman.pdf)). The exact different orders at 101 prove \(P_0\) is nontorsion over K.

The two conjugate j=1728 elliptic curves are isomorphic by scaling \((x,y)\mapsto(u^2 x,u^3y)\) with \(u=(3+\sqrt2)/\sqrt7\). Every geometric cross homomorphism is this fixed isomorphism composed with a CM endomorphism over \(K(i)\). The automorphism fixing \(K(i)\) and negating \(\sqrt7\) therefore negates each cross homomorphism, while fixing the two conjugate K-points. A relation \(\phi(P_0)=m\overline{P_0}\) modulo torsion, with \(m\ne0\), would force \(2m\overline{P_0}\) torsion, impossible. A proper connected positive-dimensional subgroup projecting nontrivially to both elliptic factors would give such a relation for a multiple of the pair: its projections are isogenies, so compose one with the dual of the other. The identity component of the closure of the integer orbit thus must be the whole product. The same holds for an entire nontrivial integer progression of shifts. This last observation does not rule out one isolated arithmetic certificate at the literal value of the shift.

Replay (exact integer arithmetic, no coefficient expansion or prime scan): `python3 -B replay_full_chart.py | cmp - EXACT-CHART-CONTROLS.json`. It replays the old 181 and 1346909 chart calculations, verifies the new invariants/valuations, counts all 32 labeled base points combinatorially, and explicitly checks the reduction-order witness. The geometric argument is the proof above; the replay is not a substitute for the cohomology calculation. No local Lean build or remote write.
