# The fixed mover: exact integral new lattice and the two-unit toric test

Keep \(p=415721\), \(N=205042530\), \(a_p(f_N)=978\), the actual same-scale \(D\), \(h'=-2207\), \(d'=rD\), \(\Delta=h'd'\), and the [matching lift](../joined-fixed-pa-actual-toric-lift-r3/THE-ACTUAL-SIGNED-JET-HAS-A-MATCHING-WALDSPURGER-LIFT.md) and [same-place square](../joined-fixed-pa-toric-square-and-sign-r2/EXACT-TORIC-SQUARE-AND-INDIVIDUAL-SIGNS.md). Let \(g\) be any of the resulting weight-two characteristic-zero transfers reducing to the retained good packet and with the matching definite vector \(\Phi\). No selection is changed. Write \(M=Np^2\).

**Claims.** The entire localized \(p^2\)-new Betti lattice in each archimedean sign reduces modulo \(p\) to the middle old degeneracy of the exact level-\(N\) lattice. Its cup pairing divided by \(p\) is perfect. For primitive integral Betti symbols \(\eta_g^\pm\), put \(C_h=\Lambda_{\chi_{h'}}(\eta_g^-)\), \(C_d=\Lambda_{\chi_{d'}}(\eta_g^+)\), where \(\Lambda_\chi\) is the exact twisted cusp-divisor sum below. Then \(C_d\in p\mathcal O\), and \(v_p(S^2)=v_p(C_h)+v_p(C_d)-1\) for the literal toric sum \(S\) (zero cases equivalent on both sides). Consequently the original signed jet is nonzero exactly when \(C_h\) and \(C_d/p\) are both units. The residue of \(C_h\) is the **old** \(h'\)-twist symbol up to a unit, while normalized \(C_d/p\) has a precise trace-preimage readout on the old symbol. Neither unit is evaluated here.

## 1. Lattices and the actual level traces

Take a finite coefficient DVR \(\mathcal O\) above \(p\), over which all relevant weight-two eigensystems and local characters split, with maximal ideal \(\varpi\), residue \(k\) and always \(v_p(p)=1\). Coefficient extension may be ramified. At levels \(N,Np,Np^2\), localize the torsion-free integral Betti \(H^1\) of the compact complex curve at the **same anemic** maximal ideal (operators outside \(Np\), good eigenvalues of \(f_N\) modulo \(\varpi\)). Write \(H_j^\epsilon\) for the resulting eigenspace of complex conjugation \(\epsilon=\pm1\) at level \(Np^j\). At level \(j=2\) append \(+\) to indicate the \(W_{p^2}=+1\) summand, distinct from \(\epsilon\). The good Hecke correspondences are self-adjoint, hence the localized lattices are perfectly paired with their opposite archimedean sign by Poincaré; \(W_{p^2}\) is a degree-one automorphism preserving this pairing, and \(2\) is a unit. The paired summands \(H_2^{+,\epsilon},H_2^{+,-\epsilon}\) remain perfect.

Use relative modular symbols interchangeably with \(H_j^\epsilon\) in this localization. The relative-to-absolute sequence has only cusp boundary as kernel; at a cusp of level \(Np^j\) a good \(\ell\)-correspondence acts on its numerator index by the two permutations \(\ell,\ell^{-1}\) with multiplicities \(\ell,1\) on cusps (and with the adjoint convention on functions). Thus the boundary eigenvalues have reducible Eisenstein traces \(\chi(\ell)+\ell\chi(\ell)^{-1}\), excluded by the irreducible residual representation. Equivalently the cusp Galois fields here divide \(\mathbb Q(\zeta_p)\); the boundary packet is an Eisenstein one over \(\mathcal O\) and modulo \(\varpi\). These integral Betti groups are finite free; their localized relative divisor readouts are genuine functions on degree-zero rational cusp divisors. Pullback and trace of finite level maps are adjoint under Poincaré, also after this localization.

Let \(\alpha_j,\beta_j:X_0(Np^{j+1})\to X_0(Np^j)\) be the two degeneracy coverings \(z\mapsto z,pz\); their degrees for \(j=0,1\) are \(p+1,p\). See [Mazur–Ribet §13](https://math.berkeley.edu/~ribet/Articles/mazur-ribet.pdf) for the literal maps. Write trace as pushforward on Betti cohomology. At level \(Np\), the entire characteristic-zero packet is \(p\)-old: any \(p\)-new Steinberg form has local unramified ordinary quotient \(\pm1\) on arithmetic Frobenius even modulo \(\varpi\), while the actual residual quotient is \(978\not\equiv\pm1\). Exact tame conductor excludes any other old-level deletion. On the lifts
\(A(x)=\alpha_0^*x,\ B(x)=\beta_0^*x\), the two trace Gram matrices are
\[
  \begin{pmatrix}p+1&T_p\\T_p&p+1\end{pmatrix}.
\]
This is invertible over the localized lattice since \((p+1)^2-T_p^2\) has residue \(1-978^2\ne0\) at its maximal ideal. Thus \(H_1^\epsilon\) is literally the direct sum \(A(H_0^\epsilon)\oplus B(H_0^\epsilon)\), not merely isogenous: the pulls are saturated and already fill the rank in characteristic zero. The same argument is valid after every indicated coefficient extension.

At level \(Np^2\) denote the three degree-\(p^i\) old pullbacks by \(D_i\). Then
\[
 D_0=\alpha_1^* A,\quad D_1=\alpha_1^* B=\beta_1^* A,\quad D_2=\beta_1^* B.
\]
The \(W_{p^2}\) action swaps \(D_0,D_2\) and fixes \(D_1\) exactly by the [Atkin-matrix calculation](../joined-fixed-pa-depleted-symbol-obstruction-r1/P-DEPLETION-IS-NOT-THE-RETAINED-CENTRAL-SYMBOL.md). Also \(\alpha_1 W_{p^2}=W_p\beta_1\) and \(\beta_1 W_{p^2}=W_p\alpha_1\) as maps to level \(Np\). In matrix terms, if \(W_{p^2}=\bigl(\begin{smallmatrix}p^2x&y\\Np^2z&p^2t\end{smallmatrix}\bigr)\), \(W_p=\bigl(\begin{smallmatrix}pu&v\\Np w&p b\end{smallmatrix}\bigr)\), the product \(W_{p^2}(W_p\operatorname{diag}(p,1))^{-1}\) has integral entries, determinant one, and lower left entry \(Npzb-Np^2tw\), divisible by \(Np\). This proves the first equality; involutions give the second. On \(H_1\), \(W_p\) swaps \(A,B\) by the same matrix argument. The reverse-and-pull \((\beta_1)_*\alpha_1^*=U_p\) on \(H_1\): the \(p\) inverse branches are \(z\mapsto(z+j)/p\), and their trace of weight-two differentials gives the classical \(U_p\), with its \(1/p\) from pullback. Complex conjugation then gives equality on antiholomorphic cohomology, hence on the integral lattice. In particular
\[
    (\alpha_1)_*D_0=pA,\quad
    (\alpha_1)_*D_1=pB,\quad
    (\alpha_1)_*D_2=T_p B-A .
\]
The last equality uses \(W_p(\beta_1)_*D_0=W_p U_p A\); the exact equation is \(U_p A=A\,T_p-B\). Here notation such as \(T_p B\) means \(B\circ T_p\) on \(H_0\).

## 2. The signed trace is integrally onto

The full map \(D_0\oplus D_1\oplus D_2\) on three copies of \(H_0^\epsilon\) remains injective modulo \(\varpi\), including generalized packets. First, a relation \(D_1(G)=D_0(F)\) of residual symbols means \(G|\operatorname{diag}(p,1)=F\) on every degree-zero cusp divisor. The projective inverse of this matrix is in the same tame double coset. Since \(F,G\) are base-level invariant, all \(p+1\) branches give \(T_pG=(p+1)F\) and \(T_pF=(p+1)G\). Invertibility of \((p+1)^2-T_p^2\) proves both zero. For all three terms, apply \(U_p\) (at level \(Np^2\)) modulo \(\varpi\). It gives \(D_0(T_pF)-D_1(F)\) from the first term and kills the last two since \(U_pD_i=pD_{i-1}\) for \(i\ge1\). The two-term independence gives \(F=0\), and \(W_{p^2}\) treats the remaining two. These proofs take place on the actual divisor functions via the non-Eisenstein identification, not just their characteristic-zero eigenvalues.

Let
\[
  L^\epsilon=H_2^{+,\epsilon},\quad
  P_+=(1+W_{p^2})/2,\quad
  i_\epsilon=P_+\alpha_1^*,\quad
  \lambda_\epsilon=(\alpha_1)_*:L^\epsilon\to H_1^\epsilon.
\]
On the two lower summands, \(i(A(x))=(D_0(x)+D_2(x))/2\), \(i(B(x))=D_1(x)\). The preceding independence implies each \(i_\epsilon\) injective modulo \(\varpi\), hence a saturated injection. Since opposite-sign Poincaré perfect duality makes \(i_{-\epsilon}\) adjoint to \(\lambda_\epsilon\), each \(\lambda_\epsilon\) is integrally surjective. Its kernel \(K^\epsilon\) is the literal integral \(p^2\)-new \(W_{p^2}=+\) lattice: the other trace vanishes too by the Atkin relation, and in characteristic zero their common kernel is the Atkin–Lehner new subspace. There is an \(\mathcal O\)-linear integral section \(s_\epsilon\) of \(\lambda_\epsilon\), not required to commute with Hecke.

In particular
\[
   J_\epsilon(x)=D_1(x)-p\,s_\epsilon(B(x))\in K^\epsilon,\qquad
   J_\epsilon(x)\equiv D_1(x)\pmod{pL^\epsilon}.
\]
This gives an actual integral new lift of every middle old residue, not the assertion that joint trace zero modulo \(p\) alone lifts a vector.

## 3. All characteristic-zero lines in the new packet

Let \(T_N\) denote the completed tame weight-two Hecke algebra of the matching-vector result, extended to \(\mathcal O\), and let \(r_0=\operatorname{rank}_{\mathcal O}T_N\). This is a relative count, not a numerical class or congruence computation. At level \(N\), both archimedean sign lattices are free of rank one over \(T_N\): Wiles Theorem 2.1(i) and Corollaries 1–2 give the full Tate module free of rank two and the Gorenstein dual. Betti comparison gives the cohomological version (or use the dual with the Gorenstein property); the two archimedean idempotents are direct summands over a local ring, hence free, of rank one each by the characteristic-zero normalized eigenspaces. The anemic/full equality was proved for the **actual** level \(N\) packet, not assumed at level \(Np^2\).

Every \(p^2\)-new characteristic-zero constituent of the high packet has central character one and the actual \(\bar\rho\) by good traces. We check that every such constituent has the same local cuspidal type used for \(\Phi\), using [Gee–Kisin, Thm 2.1.3 and Corollary 4.5.6 (Theorem A)](https://arxiv.org/pdf/1208.3179).

* Its conductor two at \(p\) implies tame Weil–Deligne type. In fact a nontrivial finite wild image with determinant one cannot fix exactly one line, so would contribute codimension two **and** positive Swan, forcing conductor at least three. Scalar inertia is necessarily ramified quadratic at conductor two. Twisting by the global quadratic character of discriminant \(p\) removes that inertial character, leaving a weight-two form with \(p\)-exponent at most one. But its reducible residual inertia has diagonal characters \(\eta,\eta\bar\chi_p\), neither trivial, where \(\eta\) is the nontrivial tame quadratic character. This is impossible in the ordinary or Steinberg case (unramified quotient) and in the good nonordinary case (irreducible residual restriction to \(G_{\mathbb Q_p}\), with niveau-2 inertia, by Deligne–Fontaine). Thus scalar type does not occur. Nonscalar type has zero monodromy and is potentially Barsotti–Tate at \(p\).
* For the actual good ordinary nonsplit \(\bar\rho\), the only possible Breuil–Mézard supporting weights are \(\mathbf1\) and \(\mathrm{Sym}^{p-1}\). In ordered subquotient convention the stable inertia character is \(\bar\chi_p\) and the quotient trivial. The reducible-weight rule requires \(\omega^{m+n+1}\), \(\omega^m\) in that order for the weight \(\det^m\mathrm{Sym}^n\), yielding \(m=0,n=0\) or \(p-1\). The order cannot switch because of nonsplitting; in particular a tame split recipe cannot be used. See [Wiersema §4.1, Kisin’s weight rule, and §3](https://arxiv.org/pdf/2004.07587). Equivalently use the nonsplit cyclotomic-ratio case of the predicted-weight theorem (the actual good crystalline lift makes the weight-two case nonempty). Gee–Kisin's Hodge–Tate sign uses the dual convention; dualize the residual Galois representation and local character when applying it there. These two finite-group weights are self-dual, and all the principal/cuspidal character tests below are unchanged under inversion.
* A nonscalar tame principal series type of finite \(\mathrm{GL}_2(\mathbb F_p)\) has Jordan–Hölder weights of dimensions \(j+1,p-j\), where \(1\le j\le p-2\) is the ordered difference of the two diagonal character exponents. Neither has dimension 1 or \(p\). Explicitly for exponents \(b+j,b\) the weights are \(\mathrm{Sym}^j\det^b\) and \(\mathrm{Sym}^{p-1-j}\det^{b+j}\). Their Brauer characters give the induced character on scalars, the two endpoint terms on distinct split eigenvalues, and zero on nonsplit eigenvalues (one full geometric progression of length \(p+1\)).
* A tame cuspidal type of central character one has residue parameter \(z\mapsto z^{j(p-1)}\) up to inversion, \(1\le j\le(p-1)/2\) (exclude the scalar and nonregular quadratic). Its two Jordan–Hölder weights are
\[
       \mathrm{Sym}^{\,2j-2}\det^{\,1-j}
       \quad\hbox{and}\quad
       \mathrm{Sym}^{\,p-1-2j}\det^{\,j}.
\]
For completeness on distinct split eigenvalues \(x,y\), write \(u=x/y\). Their exponents in \(u\) combine into the interval \(1-j,\dots,p-1-j\) of length \(p-1\), giving zero. On nonsplit \(y=x^p\), one has \(y^{p-1}=u\); the second interval shifts by one. The union is a full cycle of length \(p+1\) less the exponents \(j,-j\bmod p+1\); the sum is \(-u^j-u^{-j}\), the cuspidal character. Dimensions on scalars give \(p-1\). Brauer character uniqueness proves the formula from the ordinary finite cuspidal character table (e.g. [File–Martin–Pitale, depth-zero character calculation](https://msp.org/ant/2017/11-2/ant-v11-n2-s.pdf)). The Steinberg weight cannot occur by dimension; the trivial one occurs only at \(j=1\) (at the other dimension-one endpoint the character is the nontrivial quadratic determinant). This is exactly the original \(\widetilde\tau^{\pm1}\) type.

A potentially Barsotti–Tate lift in the given nonscalar type forces intersection with the supported Serre weights by the cited positive Hilbert–Samuel multiplicity formula. This proves that every high \(p^2\)-new constituent, not just a chosen \(g\), is in the single cuspidal type \(\widetilde\tau^{\pm1}\). All have \(W_{p^2}=+\) by the same central-one local epsilon calculation, and fixed tame signs by their actual \((1+\ell)U_\ell\) residual traces.

The **whole generalized** localization of the \(\tau\)-framed quaternion space modulo \(\varpi\) has dimension \(r_0\). Indeed the same Hasse exact sequence as in the matching-vector proof has zero localized \(H^0(\omega^{p-1})\) (its weight exclusion proved absence of the entire packet), and \(H^1(\omega^{p-1})=0\) by negative degree duality. Hence the framed space is semilinearly isomorphic to the whole localized \(H^1(\mathcal O)\), the regular \(T_N/\varpi T_N\)-module with the stated Hecke normalization. This is stronger than its one-dimensional socle statement. The finite quaternion function lattice reduces onto this space. In characteristic zero every constituent has one \(\widetilde\tau\)-axis and the literal tame new lines. By Jacquet–Langlands and strong multiplicity one it follows that there are exactly \(r_0\) geometric characteristic-zero lines in the high \(p^2\)-new packet and thus \(\operatorname{rank}K^\epsilon=r_0\) in either archimedean sign. No numerical value of \(r_0\) is assumed.

The map \(J_\epsilon:H_0^\epsilon\to K^\epsilon\) just constructed is an isomorphism of finite free \(\mathcal O\)-modules: the ranks coincide and it is injective modulo \(\varpi\) in the ambient lattice, whose new kernel is saturated. Modulo \(p\) (not just modulo \(\varpi\)) its reduction in the ambient lattice is \(D_1\). It intertwines all good and tame residual Hecke operators modulo \(p\), because the correction to \(D_1\) is \(p\) times an integral vector and \(K^\epsilon\) is saturated. This argument works for a ramified coefficient ring as written. In particular every primitive integral new \(g\)-symbol reduces modulo \(\varpi\) to the same actual old \(f_N\) symbol carried by \(D_1\), up to a unit: the good eigenspace of the regular \(T_N/\varpi\) module is its one-dimensional socle. There is no assumption of a saturated spectral projector onto an individual characteristic-zero line.

## 4. Exact elementary divisors and the norm comparison

The matrix of \(G_\epsilon=\lambda_\epsilon i_\epsilon\) on the **entire** lower lattice is triangular by the actual formulas of §1:
\[
      A(x)\longmapsto \frac{p-1}{2}A(x)+\frac12 B(T_p x),
      \qquad B(x)\longmapsto p B(x).
\]
Thus \(\mathrm{coker}\,G_\epsilon\simeq H_0^\epsilon/pH_0^\epsilon\) as an \(\mathcal O\)-module. The pairing cokernel of \(K^{-\epsilon}\to(K^\epsilon)^*\) is exactly the same kind of module. Indeed \(K^\epsilon\) is a direct summand as an \(\mathcal O\)-module, so \(L^{-\epsilon}\to(K^\epsilon)^*\) is onto by perfect Poincaré. Its kernel is \(i_{-\epsilon}(H_1^{-\epsilon})\) by adjunction and that image's saturation. Modding out also by \(K^{-\epsilon}\), then applying the onto trace \(\lambda_{-\epsilon}\), gives \(\mathrm{coker}\,G_{-\epsilon}\). Therefore all \(r_0\) elementary divisors of the opposite-sign new cup pairing are \(p\) up to units. In a ramified coefficient ring this means divisor \(\varpi^{v_\varpi(p)}\), not \(\varpi\). **Dividing the cup pairing by \(p\) makes it perfect integrally.**

On the integral \(\widetilde\tau\) quaternion function lattice the bilinear pairing between opposite axes is perfect too. The product functions are invariant under the full unit subgroup; every unframed marked supersingular point has only scalar geometric automorphisms. There are
\[
   n_{\rm ss}=(p-1)\prod_{\ell\mid N}(\ell+1)/12
\]
such points, by the Hasse divisor degree (Hodge degree is \(\prod_{\ell\mid N}(\ell+1)/12\)). This is a \(p\)-unit. The Tamagawa Petersson pairing is \(2/n_{\rm ss}\) times the coordinate sum of products, hence perfect over \(\mathcal O\) in the two opposite phase bases. Localization at the common good ring remains perfect since all the good Hecke operators are self-adjoint. The specific \(R(u)\) from the actual dual torus uniformizer exchanges the two integral axes by permutation and root-of-unity frame factors, so
\[
        (x,y)\longmapsto \langle x,R(u)y\rangle_{\rm Pet}
\]
is a perfect balanced pairing on the single integral quaternion packet. This is the **whole localized packet**, not the restriction of a perfect pairing to one congruent eigenline.

Let \(A_g\) be the order generated by the good Hecke vectors in the product of the \(r_0\) characteristic-zero coefficient factors (work over a common splitting DVR). It is the same order acting faithfully on the quaternion lattice and each \(K^\pm\), since their entire characteristic-zero systems were matched. All three modules are cyclic mod \(\varpi\) over this order: for the quaternion lattice use the Hasse generalized-packet isomorphism, and for \(K^\pm\) use middle-degeneracy comparison. Nakayama then gives cyclic integral modules, and faithfulness identifies each with the regular \(A_g\)-module. In particular no integral eigenprojector onto a single \(g\) exists in this regular quaternion module if \(r_0>1\): the local order has no nontrivial idempotents. This is not a problem for the lattice comparison.

On the regular module any balanced perfect \(\mathcal O\)-pairing is \((x,y)\mapsto\lambda(xy)\) for a generator \(\lambda\) of the \(A_g\)-dual of \(A_g\). Two such pairings differ by an \(A_g\)-unit. Identify the two Betti lattices and the quaternion lattice with \(A_g\) as above. A primitive generator of an individual \(g\)-line maps to a primitive generator under each such isomorphism, so the choices of primitive scales differ only by \(\mathcal O^\times\). Taking the two opposite arch signs on one side and the \(R(u)\)-paired axes on the other yields for their nonzero eigenline pairings
\[
       v_p\!\left(\frac{\langle\Phi,R(u)\Phi\rangle_{\rm Pet}}
                       {\langle\eta_g^+,\eta_g^-\rangle_{\rm cup}}\right)=-1.
\]
This comparison does not assert that either individual pairing is a unit on a congruent eigenline. It tracks the common congruence factor through the two full perfect lattices.

## 5. Corrected CST arithmetic and the actual divided functional

Let the primitive relative symbol \(\eta_g^\epsilon\) be normalized by \(2\pi i\,g(z)dz\) and a cohomological period \(\Omega_g^\epsilon\), with \(\epsilon=\pm\) the actual complex conjugation sign. Set
\[
   \Lambda_\chi(\eta)=
        \sum_{b\bmod m}\chi(b)\,\eta(\{\infty\}-\{b/m\}),\quad
         m=\operatorname{cond}(\chi).
\]
For \(\chi_{h'}\) use the minus sign, for \(\chi_{d'}\) the plus sign. Finite Gauss summation of the translated Fourier expansion gives \(C_\chi=\pm\tau(\chi)L_{\rm fin}(g^\chi,1)/\Omega_g^\epsilon\), where the sign depends just on the chosen divisor orientation. Integral relative cusp symbols here are the preceding non-Eisenstein lattice, so \(C_\chi\in\mathcal O\). The primitive local factors at primes dividing the twist conductor are actually one: the common tame level primes become ramified Steinberg twists with no invariants, and at \(p\) the regular cuspidal type stays regular. Thus the finite Dirichlet-twisted Fourier \(L\)-function is the primitive one in the stated comparison, not an imprimitive adjustment. The product Gauss factors have valuation \(1/2\), since only \(d'\) is simply divisible by \(p\).

For clarity keep the completed factors of [CST (2.1), Prop. 1.11, and Lemma 3.14](https://arxiv.org/pdf/1408.1733). Write \(P_g\) for the classical weight-two Petersson integral over \(X_0(M)\), and \(B_g=\langle\eta_g^+,\eta_g^-\rangle_{\rm cup}\). The classical Riemann bilinear relation for \(2\pi i g(z)dz\) gives \(\Omega_g^+\Omega_g^-/P_g=\pm4\pi^2 i/B_g\) with the choice of orientation/period sign; a factor of 2 from changing the plus/minus convention would be a \(p\)-unit and is not used here. This follows by writing the class of \(2\pi i gdz\) as the sum of its two cohomological periods times the primitive classes, then integrating its wedge with its conjugate. One may choose the periods real and purely imaginary respectively (the coefficients of \(g\) lie in a totally real number field); a primitive \(\mathcal O\)-scale is obtained by rescaling at the chosen place and does not alter the valuation.

In the CST convention the torus period per class is \(2/\sqrt{|\Delta|}\), the Rankin archimedean factor is \(\Gamma_{\mathbb C}(1)^2=\pi^{-2}\), \(L(2,1_{\mathbb Q})=\pi/6\), and \(\beta_\infty=1/\pi\) (equivalently use Lemma 3.14 with \(\alpha_\infty=2^{-2}\)). Proposition 1.11 gives
\[
       L(1,\mathrm{ad}\,g)/P_g=(4/M)L_p(1,\mathrm{ad}\,g),
        \qquad L_p(1,\mathrm{ad}\,g)=(1+p^{-1})^{-1}.
\]
Here the norm of the integral conductor in that proposition is \(M\), and \(p\) is its only prime of exponent at least two. The corrected CST equation for the same-place square \(S^2\) now has no uncancelled transcendental factor: substitute these expressions, the Gauss readout, and the cup relation. Its multiplier of \(C_h C_d\), up to a factor in \(\{\pm i/48\}\), is
\[
   M|\Delta|\,
   \frac{\langle\Phi,R(u)\Phi\rangle_{\rm Pet}}{B_g}\,
   \frac{1}{L_p(1,\mathrm{ad}\,g)\,\tau(\chi_{h'})\tau(\chi_{d'})}\,
   \prod_{\ell<\infty}\beta_\ell .
\]
The finite factors away from \(p\) are \(p\)-units: at unramified spherical places they are 1, at good ramified places \(\ell^{-1/2}\), and at the fixed tame level primes the unramified or ramified Steinberg expressions are products of powers of small \(\ell\), \(2\), and factors \(1\pm\ell^{-1},1-\ell^{-2}\), none divisible by \(p\). These are the cases \(n=c=0\), split \(n=1,c=0\), and ramified \(n=1,c=0\) of CST Proposition 3.12. At \(p\), \(\beta_p=(1-p^{-1})/\sqrt p\) by the half-mass selected axis calculation. In order, the valuation contributions are \(3,-1,-1,-1/2,-3/2\), totaling \(-1\). All comparisons are at the same place, under arbitrary finite extensions with \(v_p(p)=1\); a square root or a Gauss sum is not replaced by an absolute norm at another place. This proves the announced valuation identity and also treats zero values by the same nonzero multipliers.

Finally, if \(p\mid m\) exactly and \(\chi\) is primitive at \(p\), then \(\Lambda_\chi(D_1(x))=0\) **exactly** for every old \(x\). Multiplying a numerator by \(p\) makes the cusp depend only on that numerator modulo \(m/p\); the sum of the nontrivial local character on each \(p\)-fibre is zero. Since \(J_\epsilon\) is an isomorphism and differs from \(D_1\) by a literal \(p\) times an integral symbol, it gives \(p\mid C_d\) even over a ramified DVR. More precisely, for any integral \(\lambda_+\)-preimage \(z\) of \(B(\eta_{f_N}^+)\) in the localized upper \(W_{p^2}=+\) lattice,
\[
      \frac{C_d}{p}\bmod\varpi
        \ \in\ k^\times\!\cdot
              \bigl(-\Lambda_{\chi_{d'}}(z)\bmod\varpi\bigr),
\]
where the statement means equality up to a fixed nonzero scalar, including the zero case. The residue is independent of the preimage because their differences lie in \(K^+\), where every such ramified functional is divisible by \(p\). This follows by using \(J_+\) to pull \(\eta_g^+\) to \(H_0^+\) and reducing its old representative to the unique actual old eigensymbol. For \(h'\), reindexing numerators at conductor prime to \(p\) gives \(\Lambda_{\chi_{h'}}(D_1(x))=\chi_{h'}(p)^{-1}\Lambda_{\chi_{h'}}(x)=\Lambda_{\chi_{h'}}(x)\), so \(C_h\bmod\varpi\) is the old \(h'\) symbol up to a unit.

The finite new input is therefore the one integral trace preimage \(z\) (independent of the varying \(d'\)), followed by the exact varying signed divisor functional. For the smaller fixed-factor diagnostic \(m_0=1577,\ d_0=p m_0\), the same two-unit test applies (the split-vs-ramified tame factor changes are \(p\)-units). It predicts an exact falsifiable comparison with the normalized, oriented full toric sum on that diagnostic. Neither that trace preimage nor its diagnostic or production value has been computed. No analytic rank, rational point, or selected-ray nonzero is asserted.
