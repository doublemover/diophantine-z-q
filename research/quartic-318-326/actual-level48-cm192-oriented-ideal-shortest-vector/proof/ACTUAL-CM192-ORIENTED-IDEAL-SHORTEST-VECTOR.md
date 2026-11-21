# Recover the coherent CM sign by one degree-eight shortest-vector calculation

Once the exact **oriented primes over good rational primes** of the Heegner norm-one ideal are known, the next marking sign can be computed without a class group, a cyclic class-field character, a global Heegner point, or its coordinates. The two bad prime components at 2 and 3 can simply be omitted. A coordinate lattice of the resulting fractional ideal has a known minimum and exactly two shortest vectors, which are the two signs of its norm-one generator. This is an exact receiver; the good oriented ideal has not been computed for an original detector.

## 1. Both bad-place valuations are explicit and removable

Use the actual balanced twists, full oriented level-48 class orbit, the quadratic \(K=\mathbf Q(\sqrt D)\) for \(D=-n\), the relative field \(L=K(\sqrt3,\sqrt{17})\), and the norm-one product \(U\in L\) of the marked cyclic-four receiver. Here \(h=|\mathrm{Cl}(K)|\); the product is normalized by \(12^{h/8}\) and the \(\chi_{17}=+\) half-orbit of \(h_T=y/(x-3)-(2+\sqrt3)\). For this result assume the original \(n\equiv23\bmod24\) refinement and its literal support \(\beta\) containing 17 and six distinct genuine primes.

We use two exact eta quotients on the literal modular map:
\[
 x\circ\phi=\eta_4^{-2}\eta_8^4\eta_{12}^{2}\eta_{24}^{-4},
 \qquad
 (x+1)\circ\phi=\eta_2^{-1}\eta_6^3\eta_8\eta_{24}^{-3}.
\]
The second is the forgetful pullback of \(x_{24}\) in [Colò, Appendix A, pp. 245, 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf). For the first, \(x\circ\phi=y_{48}/X^2\) gives its exact divisor \(2[1/8]+2[1/16]-2[1/24]-2[\infty]\) from the long-coordinate divisors. Newman–Ligozat checks that the displayed eta quotient is a modular function with exactly this divisor. Its leading coefficient at \(\infty\) is one, as is the leading coefficient of \(x\circ\phi\) because \((x+1)\circ\phi\) has that coefficient and a pole there. This derivation does not depend on the duplicated \(y_{48}\) eta line in the printed thesis.

At each of 2 and 3 choose the place at which the prescribed level arm is connected and call it \(\mathfrak p_p\) in \(K\); the conjugate arm is étale. With \(v_p(p)=1\), the good CM differential argument of the fourth-divisibility proof gives \(v_p(f)=0\) on the connected arm of any such eta quotient, and \(-\frac12\sum_d r_d v_p(d)\) on the étale arm. The weights for \(x\circ\phi\) are \(0,-2\) at 2,3 respectively, and for \((x+1)\circ\phi\) they are \(-4,0\). Fricke sends the original level arm to the opposite arm, and \(x\circ J=3(x+1)/(x-3)\) for \(J=T_3-\). So, for every CM index, the paired valuations are
\[
\begin{array}{c|cc|cc}
 &\multicolumn{2}{c|}{p=2}&\multicolumn{2}{c}{p=3}\\
 &\text{connected}&\text{étale}&\text{connected}&\text{étale}\\
 x&0&0&0&1\\
 x+1&0&2&0&0\\
 x-3&0&2&0&1 .
\end{array}
\]
The computation uses minimal good differentials on the underlying CM elliptic curves after extension, not smooth reduction of the modular curve itself at 2 or 3. All entries hold uniformly for the whole class orbit at that chosen arm.

Put \(u_0=y/(x-3)\), so \(u_0^2=x(x+1)/(x-3)\). It is a unit in each row. Modulo 2 on the connected arm \(u_0^2=x\bmod2\ne1\), because \(x+1\) is a unit. On the étale arm write \(z=(x+1)/4\); both \(z,z-1=(x-3)/4\) are units and \(x\equiv1\), hence \(u_0^2=z/(z-1)\ne1\) in the residue field. At 3 on the connected arm \(u_0^2=x+1\bmod3\ne1\) since \(x\) is a unit. On the étale arm write \(z=x/3\); again \(z,z-1\) are units and \(u_0^2=z/(z-1)\ne1\). The comparison constant \(2+\sqrt3\) reduces to an element of square 1 at both primes. Consequently
\[
             v_p(h_T(P_{\mathfrak a}))=0
        \qquad(p=2,3\text{ on either arm, for every }\mathfrak a).
\]
The subset product \(M\) is therefore a unit even without computing or enumerating its subset, and \(f_T=h_T^2(x-3)\) has the exact \(x-3\) valuation. Since \(C_4^4=\prod f_T(P_{\mathfrak a})\), the normalized valuations of \(U\) at 2 are \(-h/4,+h/4\) on the connected and étale arms, and at 3 they are \(-h/8,+h/8\). These match the extension from \(K\) of the ideal
\[
        \left(\frac{\bar{\mathfrak p}_2}{\mathfrak p_2}\right)^{h/4}
        \left(\frac{\bar{\mathfrak p}_3}{\mathfrak p_3}\right)^{h/8}.
        \tag{1}
\]
At both primes the absolute ramification index in \(L\) is two (from \(\sqrt3\)); integer ideal orders in \(L\) are twice the listed normalized orders.

Crucially one need not compute \(h\) or generate (1). Choose four independent ramified classes of \(K\), e.g. 17 and any three genuine primes of the \(\beta\) support. Each nonempty subset has integral nonsquare norm \(<n/4\) and cannot be principal by the norm lower bound for nonrational integers of \(K\), so they generate a subgroup \(C_2^4\). Every cyclic subgroup meets it in at most two elements, hence \(h/8\) kills all \(\mathrm{Cl}(K)\). Thus \(\bar{\mathfrak p}_2^{h/4}\bar{\mathfrak p}_3^{h/8}=(\alpha)\) in \(K\) for an \(\alpha\) supported only at 2,3. The factor \(\alpha/\bar\alpha\) has norm one, and reduces to \(+1\) at every odd ramified comparison prime since \(\alpha\) is a unit there and conjugation fixes its residue. Therefore just delete all 2,3 prime terms from the ideal of \(U\); the resulting ideal is
\[
 \mathfrak U_{\rm good}=(U_{\rm good}),\qquad
 U_{\rm good}=U/(\alpha/\bar\alpha),\quad
 U_{\rm good}\bar U_{\rm good}=1 ,
\]
with exactly the same two residue signs. No arithmetic computation of \(\alpha\) is needed. This bad-place removal applies to both actual arms under the stated common hypotheses.

## 2. The exact lattice, minimum and finite receiver

Use the degree-eight biquadratic-compositum realization
\[
 r=\sqrt3,\quad s=\sqrt{17},\quad t=\sqrt{D/17},\quad R=n/17>0,\quad L=\mathbf Q(r,s,t).
\]
In fact the integral model is explicit:
\[
 O_L=\mathbf Z\bigl[r,(1+s)/2,(1+t)/2\bigr].
\]
The three quadratic discriminants \(12,17,D/17\) are pairwise coprime, and the coprime-discriminant integral-basis theorem gives the tensor basis. The fields are linearly disjoint in the required successive composita: \(D/17\) has the fresh \(q_0\) and the genuine prime support, not present in the first two fields. Thus one may form the exact fractional ideal \(\mathfrak U_{\rm good}\) from the oriented prime factors in this explicit order, using exact rational or integral-basis ideal products. The oriented prime itself, not solely its rational support or norm, is necessary.

The only roots of unity of \(L\) are \(\pm1\). It is multiquadratic, so a root of unity of order \(a\) would have \((\mathbf Z/a)^\times\) of exponent at most two, forcing \(a\mid24\) (odd primes above 3 and higher 3-powers are excluded, and powers of 2 higher than 8 have units of order at least four). A nonreal such root would include \(i\) or a primitive cube root of unity. But every imaginary quadratic subfield has radicand of squareclass \(D/17\) times \(1,3,17,51\), keeping the genuine odd prime factors (and \(q_0\)). Neither \(-1\) nor \(-3\) is among them.

Use the positive definite rational Gram form
\[
                   \langle a,b\rangle=\operatorname{Tr}_{L/\mathbf Q}(a\bar b).
\]
In the ordered radical basis \(1,r,s,rs,t,rt,st,rst\) it is exactly
\[
                 8\,\operatorname{diag}(1,3,17,51,R,3R,17R,51R).\tag{2}
\]
Indeed mixed terms are traces of nontrivial radical monomials and vanish by the eight sign automorphisms. For a diagonal term the conjugation sign on the imaginary radical cancels the negative square \(t^2=-R\). If \(M\) is the rational matrix of coordinate columns of any \(\mathbf Z\)-basis for \(\mathfrak U_{\rm good}\), its exact rational Gram matrix is \(M^{\mathsf T}(2)M\). This computes all constants without numerical embeddings. If using integer Hermite basis over the integral order above, convert by the three tensor changes \((1+s)/2,(1+t)/2,r\), or evaluate the same trace directly.

Any nonzero element of \(\mathfrak U_{\rm good}\) is \(U_{\rm good}z\) for \(z\in O_L\setminus\{0\}\). Norm-one multiplication is an isometry, because \(U_{\rm good}\bar U_{\rm good}=1\). The arithmetic–geometric mean inequality gives
\[
 \operatorname{Tr}(z\bar z) \ \ge\ 8\,|N_{L/\mathbf Q}z|^{1/4}\ \ge\ 8,
\]
as \(N(z)\) is a nonzero integer. Equality means all absolute embedding values are one, so \(z\) is a root of unity (Kronecker's theorem), hence \(z=\pm1\). Thus the fractional ideal's minimum squared length is **exactly 8**, and its only two shortest elements are \(\pm U_{\rm good}\).

This gives a proof-producing finite algorithm:
1. Supply the exact oriented good-prime ideal and a rational basis of it. Use (2) to calculate its Gram form.
2. Solve the exact integral equation \(m^{\mathsf T}\operatorname{Gram} m=8\), for \(m\in\mathbf Z^8\). A short certificate is one returned vector, plus arithmetic checks of norm one and equality of its principal ideal with \(\mathfrak U_{\rm good}\). The theorem above guarantees a solution, unique up to sign, for a correct ideal.
3. Reduce it at places above the fresh \(q_0\) and one genuine \(p_\beta\). These values are \(\pm1\) by the coherent cyclic-four proof; changing the generator's sign switches both. Opposite residues certify the marked quarter and nontorsion; equal residues mean only that the raw trace is an eighth multiple.

One can solve step 2 by exact rational-gram LLL followed by bounded Gram–Schmidt enumeration. With Lovász parameter \(3/4\) and size reduction, \(\|b_i^*\|^2\ge\frac12\|b_{i-1}^*\|^2\), starting at \(\|b_1\|^2\ge8\). Hence at radius \(\sqrt8\) each successive coordinate lies in an interval of length at most \(2\cdot2^{(i-1)/2}\), independently of the coefficient bit lengths. The search has fixed dimension and polynomial bit cost in the **expanded exact basis**; this is not a bound in the size of the discriminant alone or a way to manufacture the unknown oriented good-prime ideal. A norm of the ideal, or an unsigned product of class polynomials, is not a replacement for it.

## 3. Mod-four intersection exponents suffice for a class route on the first arm

The exact shortest-vector method needs the full principal fractional ideal. If using an optimal class character instead, there is a separate arithmetic saving for the first selected arm \(u=1\) with no repair. Any prime \(\mathfrak P\) in the remaining good-prime support has \(2\)-primary ideal class of order at most four. For \(p>3\) different from 17, both CM fields must be nonsplit for a genuine collision, and the ramified \(p\mid n,\ p\ne17\) signed terms cancel by the existing inertia proof. Thus any nonzero remaining such \(p\) is inert in \(K\). Its residue degree in the multiquadratic \(L\) is two. The ideal norm to \(K\) is principal: it is \((p)\) in the inert quadratic. For each of the three other imaginary quadratic subfields the norm is either the principal inert ideal or the square of a prime ideal (at a split prime), which is trivial in the \(2\)-primary group since those subfields have exponent at most two. The four-norm identity therefore gives \(4[\mathfrak P]_2=0\).

The same conclusion holds at 17. The actual mark at 17 ensures \(n/\beta\) is a square unit, and the six genuine support primes are \(1\bmod17\), so \(D/17\) is a square in \(\mathbf Q_{17}\). In the four imaginary subfields, 17 is ramified in \(K_0,K_2\), split in \(K_1\), inert in \(K_3\). The absolute residue degree in \(L\) is two. Norms to the ramified subfields are squares of ramified prime ideals and hence principal; the split subfield receives a square and has \(2\)-primary exponent at most two; the inert one receives a principal ideal. Again \(4[\mathfrak P]_2=0\). Since its signed exponent is even by the exact 17 parity theorem, only one bit modulo four remains there for the class computation.

Consequently a **character evaluation** needs the oriented good intersection exponents only modulo four, not modulo sixteen or higher, despite the minimal character order on the marked class. An odd-order component of such ideal classes is immaterial for that evaluation. This does not permit reducing exponent data modulo four and treating the result as the exact principal lattice of §2. Both routes still require a genuine oriented intersection input: either full exponents for the norm-one element, or their class-sign evaluation.

### Exact dependencies and replay

- *The first half of the raw level-48 detector trace is unmarked*, paper **bbfe4e889f688bcf69f8b643fc60615fb0945ff0ab1862ff21e28127744535f3**, supplies the CM differential valuation and fixed level model.
- *The next detector saturation sign is an oriented CM intersection ideal*, paper **c83ce5b2c7d6c95283d67f375f3c306f8ed62ead52c344c78d33ba991724ae7e**, and *The next marked sign from a relative ideal-class relation*, **7500994322c7257e29c58aa2411f77e23276a49871c4cd7ae1c893db73c45e4d**, supply the exact norm-one generator and first-quarter signs.
- *Exact separating character order on the original first arm*, **3f0cf36a6b7e4ad25e1d6b39681cc748797c0320e54a55fbc1a3c2481eb23530**, supplies the four-field norm identity and the auxiliary class exponents needed only in §3.

The exact replay checks eta exponents/cusp orders, weights at 2,3, and the trace Gram constants. It computes no marked residue or actual Heegner ideal.

    python3 -B replay_oriented_ideal_local_and_gram.py | cmp - EXACT-ORIENTED-IDEAL-LOCAL-AND-GRAM.json
    sha256sum -c SHA256SUMS
