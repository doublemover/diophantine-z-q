# A moving degree-24 class-group bound suffices for one actual detector companion

Fix one of the three original detector poles at the common index of the four-Ready/anchor source. Fix a member $E_n:y^2=x(x-n)(x+3n)$ of its exact balanced pair, with the same marked class $(\beta,1)$, root number $-1$ and $\#\operatorname{Sel}_2(E_n)=8$. Here $n>0$ is squarefree, $n\equiv11\pmod{12}$ and $17\mid n$. Arrange $5\nmid n$ on the chosen arm: the fixed $\beta$ support avoids 5, assign all of $\theta$ to the other arm and choose the fresh helpers and final prime away from 5. This includes the original split with one side equal to 1 and does not change the literal pole. There is no computed $n$ or class group here.

**Sufficient arithmetic certificate.** There is a fixed degree-six line field $D$ with a fixed quadratic extension $D_2/D$ and a fixed nonzero $\alpha\in D_2$ such that the companion-specific degree-24 field is
$$
 A_n=D_2(\sqrt{(-n)\alpha}).
$$
It is cyclic quartic over $D$. Fix its generator $\sigma_2$ by the mod-5 covector condition below. Let $\mathrm{Cl}_{S}(A_n)$ be the ordinary class group with the classes of all primes above $S=\{2,3,5\}$ killed. One can also kill the primes above all rational primes dividing $n$ if known. Define
$$
 \mathscr W_n=
 \left\{W\in\operatorname{Hom}\bigl(\mathrm{Cl}_{S}(A_n),\mathbb F_5\bigr):
       W(\sigma_2\mathfrak a)=2W(\mathfrak a)\ \text{for every }\mathfrak a
 \right\}.
$$
The finite certificate $\dim_{\mathbb F_5}\mathscr W_n\le1$ implies rank one and makes the literal mark rational on this companion. Using the full class group instead of $\mathrm{Cl}_{S}$ is also sufficient with the same bound. This is not a claimed value of the dimension, or an identification of $\mathscr W_n$ with the Selmer group.

## 1. Exact local inputs on this selected arm

At 3 the integral model has $v_3(\Delta)=2$, $c_4$ a unit, and the singular tangent has slopes determined by $-n\equiv1\pmod3$. Thus this is split Tate multiplicative reduction of type $I_2$. Its local point group is $\mathbb Q_3^\times/q^{\mathbb Z}$ with $v_3(q)=2$. It has no 5-torsion: the valuation quotient has order two and the unit group has pro-3 subgroup and residue group of order two. At 2, $v_2(\Delta)=8$ on the displayed integral model (so it is minimal, as a change to smaller discriminant would subtract a multiple of twelve). Its reduction is $y^2=x^3+x$ with singular point $(1,0)$ and double tangent there, hence additive reduction. The connected smooth reduction group has order two and an additive fibre has at most four geometric components, so there is no 5-torsion at 2 either. At every odd $\ell\mid n$, the base curve before twisting is good. The quadratic twist of odd valuation acts as scalar $-1$ on 5-torsion under some inertia element; thus there is no local rational 5-torsion at such $\ell$.

For $\ell\ne5$ the local formal subgroup has unique division by 5 and the finite quotient has equally sized kernel and cokernel for multiplication by 5. This proves $E_n(\mathbb Q_\ell)/5=0$ at every named bad prime. At any good prime away from 5 the 5-Kummer image is unramified by the finite étale multiplication map on the good integral model. At infinity the 5-Kummer group is zero. At 5, the base $E_{-1}$ has eight points over $\mathbb F_5$ and trace $-2$; any good quadratic twist has four or eight points and is ordinary. Reduction therefore removes no 5-quotient and the good formal logarithm gives $\dim_{\mathbb F_5}E_n(\mathbb Q_5)/5=1$.

For the full image take $V_0=E_{-1}[5]$ and $L_0=\mathbb Q(V_0)$. The base curve has trace zero at good 7 (eight points including infinity); its Frobenius polynomial has discriminant $-28\equiv2\pmod5$, a nonsquare. This gives irreducibility, also for any twist, regardless of whether the *twisted* curve is good at 7. The split Tate curve at 3 with parameter valuation two has a nontrivial 5-transvection on inertia: the fifth root of the Tate parameter has ramification degree five over the unramified cyclotomic local extension. An irreducible subgroup with a transvection contains two order-five full root groups with distinct fixed lines, by conjugating the transvection and taking powers over the prime field. In a basis of the two lines these generate $\mathrm{SL}_2(\mathbb F_5)$. The determinant is the surjective cyclotomic character, so the full image is $\mathrm{GL}_2(\mathbb F_5)$, both for the base and the selected twist.

Let $V=E_n[5]$ and $L_n=\mathbb Q(V)$. For its residual group $G=\mathrm{GL}_2(\mathbb F_5)$, the central element $-I$ gives $H^1(G,V)=0$: central conjugation acts trivially on cohomology, while its coefficient action is multiplication by $-1$, so twice every class is zero. Inflation--restriction consequently injects global $H^1(\mathbb Q,V)$ into the equivariant homomorphisms from $G_{L_n}$ to $V$.

## 2. Covector projection without a norm across degree twenty

Let $\mathcal S^0$ be the kernel of the localisation of $\operatorname{Sel}_5(E_n)$ at 5. Fix a nonzero covector $\lambda:V\to\mathbb F_5$. If $H$ is its stabilizer then $A_n=L_n^H$ has degree 24: all 24 nonzero covectors form one orbit. Let $J$ be the stabilizer of its line, characterized by
$$ \lambda\circ g=a(g)\lambda,\qquad a(g)\in\mathbb F_5^\times .$$
Then $J/H=\mathbb F_5^\times$, $D=L_n^J$ has degree six, and $\sigma_2$ is the particular automorphism of $A_n/D$ obtained from $a(g)=2$. The eigencondition in the statement uses the action of $\sigma_2$ on ideals and is not interchangeable with its inverse.

For a global cocycle $c$ representing a class of $\mathcal S^0$, the evaluation $\lambda\circ c$ on the absolute $G_{A_n}$ is an additive homomorphism, independent of the representative since $\lambda$ is fixed on $G_{A_n}$. It is trivial on the local decomposition groups above $S$, since the original class vanishes there, and also above the bad odd primes dividing $n$. At every remaining finite place it is unramified by the good-reduction local condition of Section 1 and restriction. Thus class field reciprocity gives a homomorphism from $\mathrm{Cl}_{S}(A_n)$ into $\mathbb F_5$ (only its quotient modulo 5 is relevant). No norm map or invariant-class argument across the degree-20 extension $L_n/A_n$ is used.

For a lift $g$ of the line automorphism and $\tau\in G_{A_n}$, the cocycle relation reads
$$
 c(g\tau g^{-1})
   =\rho(g)c(\tau)+(I-\rho(g\tau g^{-1}))c(g).
$$
The second term vanishes after applying $\lambda$ because $g\tau g^{-1}$ fixes the covector. The first evaluates as $a(g)\lambda(c(\tau))$. Reciprocity is equivariant for the same conjugation action on ideals, giving precisely $W(\sigma_2\mathfrak a)=2W(\mathfrak a)$.

This map from $\mathcal S^0$ is injective. If its evaluation is zero on $G_{A_n}$, it is zero on $G_{L_n}$ in particular. The restricted cocycle there is an equivariant homomorphism, so evaluating by every Galois conjugate of $\lambda$ is also zero there. Those conjugates span $V^*$ (indeed they are all 24 nonzero covectors), giving zero for the vector-valued restriction. Inflation--restriction and the calculation with $-I$ now kill the global class. It follows that $\dim\operatorname{Sel}_5(E_n)\le 1+\dim\mathscr W_n$.

Finally the negative root number makes the $5^\infty$-Selmer corank odd by [Dokchitser--Dokchitser, Theorem 4.19](https://arxiv.org/pdf/math/0610290#page=26). As $E_n(\mathbb Q)[5]=0$, a finite Selmer bound by two bounds that corank by two (the Kummer exact sequences identify the finite 5-Selmer group with the 5-torsion of the full Selmer group when rational 5-torsion vanishes). Hence the corank is one. [Yan--Zhu v4, Theorem 5.11](https://arxiv.org/pdf/2412.20078v4#page=17) gives rational rank one for this good ordinary odd prime and irreducible mod-5 image; the extra named image hypothesis there is for the BSD formula, not this equivalence. Rank one makes the full Mordell--Weil quotient at 2 fill the exact size-eight selected 2-Selmer group, supplying the required mark. This does not assert that a separately found point's own Kummer coordinates equal the mark.

## 3. The fixed subfields, and why the ordinary projective class group does not suffice

Identify the standard vector space of the twist with that of $V_0$, so $\rho_n=\chi_{-n}\rho_0$. The projective representation is fixed, and so is its stabilizer of the chosen covector line. This proves that $D$ is the same degree-six subfield of the fixed projective field. The square of the scalar character $a$ on that stabilizer is unchanged by the quadratic twist, proving that the unique degree-12 half-field $D_2$ of $A_n/D$ is fixed. The base degree-24 covector field is some $A_0=D_2(\sqrt\alpha)$. At the actual prime 17 the base mod-5 field is unramified, whereas $\mathbb Q(\sqrt{-n})$ is ramified, so the two are disjoint. Over $D_2$ the residual covector character of the base has values $\{1,-1\}$; the twist multiplies it by the independent quadratic character of $-n$. It cuts out exactly $D_2(\sqrt{(-n)\alpha})$, as asserted. This construction avoids a fresh full division field of degree 480, but leaves a genuinely moving quadratic extension.

For comparison, the fixed projective field is $P=L_n^Z$ for the scalar centre $Z$ of order four. Extension and norm identify $\mathrm{Cl}(P)/5$ with the $Z$-invariant part of $\mathrm{Cl}(L_n)/5$: their composites are multiplication by four and the scalar-group trace, respectively. The same statement holds if the corresponding split-place classes are first killed. Any equivariant map from this invariant part to $V$ vanishes because the scalar action on $V$ has no invariants. The degree-240 field fixed by $\{I,-I\}$ has the same obstruction for that subgroup. Thus an **ordinary** class-group computation in the fixed projective field does not receive the required standard-module quotient by the direct extension/norm descent. This leaves open methods that incorporate the moving scalar character as additional arithmetic data; it is not a general computational lower bound.

## Scope and exact predecessor pins

- Actual four-Ready/anchor on one eventual index: donor checksum-list `9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5`.
- Actual balanced detector eights: checksum-list `2aba4b0f33fef90976d2319160a84c81338ac33845d6f7d0b1f3df0b5364b112`. Their rank/mark and local level-48 analysis: `37f1f3207e21ae3b16d7b272d7ccfc7b6945cf976784a4781589c2fee1d41be4`.

This is a mathematical sufficiency certificate, not a computed class bound, conductor, rank, companion, or numerical source. It treats one selected arm only; another arm's point and the other poles are not supplied. Check the frozen text with `sha256sum -c SHA256SUMS`.
