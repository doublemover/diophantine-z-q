# A single explicit degree-24 class group can certify the same-twist rank exit

Let E=E_d:y²=x(x−d)(x+3d), d the **signed squarefree** representative of the nonzero indexed rational twist under consideration. Assume 5∤d. Let V=E[5] and fix a nonzero F₅-linear functional λ:V→F₅. Define K_d by the stabilizer of this **covector** in G_Q; F₅ here is the constant additive module, not μ₅. Let S contain the rational primes dividing 30d. It can also contain any finite list of good primes q∤30d with 5∤#E(F_q). Write S_K for all primes of K_d over S. Then

    dim Sel₅(E/Q) ≤ 1 + dim_F₅ Cl(O_(K_d,S_K))/5.

In particular a *certified upper bound* of one on the 5-rank of that S-class group suffices, under the previous order-eight hypotheses, for rational and analytic rank one and finite full Sha by the reviewed auxiliary odd-Selmer theorem. The present inequality itself does not need those hypotheses. We give a polynomial for this particular degree-24 field for every such d. No class group for an unavailable indexed d is being asserted. Computing only a lower bound on a class group, or silently assuming a GRH class-number calculation, is not a certificate.

**Injection by a covector.** Let L=Q(E[5]), G=Gal(L/Q). As in the odd-prime exit, E_d[5] is irreducible: on the untwisted E_1, Frobenius at 7 has trace 0, determinant 7 and irreducible characteristic polynomial mod 5; twisting by a quadratic scalar does not change lines. In fact for any lift g of this Frobenius, g² acts on V by −7I=3I, *including when d is ramified at 7* because the twisting character squares to 1. A cocycle c on G then satisfies (3−1)c(g')=(g'−1)c(3I) for all g', by comparing both products with this central element. Hence H¹(G,V)=0.

Define H¹(Q,V)→Hom_cont(G_(K_d),F₅) by c↦λ∘c restricted to G_(K_d). It is a homomorphism in the Galois variable because λ is fixed there; coboundaries evaluate to zero. If the result is zero, then in particular λ kills c(G_L). On G_L the cocycle is a homomorphism and c(g h g^−1)=g.c(h) for h∈G_L. Thus every conjugate of λ kills c(G_L). Their span is all V^∨ by irreducibility, so c vanishes on G_L and descends to a cocycle on G. Its class is zero by the previous paragraph. This proves genuine injectivity from the same actual Galois module; passing merely to the x-coordinate field of a torsion point would not justify it.

**Selmer local conditions.** At 5 the reduction has 5+1±2 points and hence no 5-torsion. The kernel of reduction is torsion-free at 5 (formal log on 5Z₅). The compact local index formula therefore gives |E(Q₅)/5|=5. The kernel of Sel₅ localization at 5, denoted Sel₅⁰, has codimension at most one.

At q∤30d the curve has good reduction; local Kummer cocycles are unramified since division by 5 of an integral point gives a finite étale torsor over Z_q. If 5∤#E(F_q), the local Kummer image is further zero because the formal kernel is pro-q. At q|d, q>3, q≠5, the ramified quadratic twist of the good curve E_1 has scalar −I on inertia after reducing modulo 5; so E(Q_q)[5]=0, and the compact local index formula at q≠5 gives E(Q_q)/5=0. At 2 the integral discriminant valuation is 8+6v₂(d) ≡8 or 2 mod12; good reduction is impossible, since changing a Weierstrass model changes this valuation by a multiple of 12. The j-invariant 35152/9 is 2-integral, so the reduction is additive. For additive reduction the component group has order at most four (Kodaira–Néron component table, including nonsplit types); the identity component of the smooth reduction has 2 points and the formal subgroup is pro-2. Thus there is no local 5-quotient. At 3, if 3∤d then the displayed model is minimal with discriminant valuation 2 and nodal special fibre, hence type I₂, component number at most 2, and torus group of order 2 or 4 over F₃. If 3|d the integral model at 3 has v₃(Δ)=8<12 and cuspidal special fibre, hence is minimal additive with component group of order ≤4 and smooth identity component of order 3. Both cases have trivial 5-quotient. Infinity has trivial 5-quotient as well.

The restricted covector character of any element of Sel₅⁰ is now unramified at all finite primes of K_d and zero on every decomposition group over S. This follows for *all* conjugate primes because the stated localization conditions hold on the Q Galois class; an evaluated coboundary on a K_d decomposition group is identically zero. At primes with good unramified classes choose an unramified representative, equivalently restriction to inertia is a coboundary; evaluation on the smaller inertia kills that coboundary. The ordinary Hilbert class field theorem identifies such characters with Hom(Cl(K_d)/⟨[w]:w|S⟩, F₅), as the Frobenius of every w|S must vanish. There is no real-place sign correction for odd-order characters. This yields the stated upper bound. Extra good primes must individually meet the stated cardinality test; arbitrary primes cannot be inserted.

**Explicit covector field, without a full torsion splitting field.** Let ζ be any primitive fifth root. The covector defined by (P,ζ), P∈E_d[5] nonzero, sends Q to log_ζ e₅(Q,P). Its equivalent presentations are precisely (aP,ζ^a), a∈F₅^×. Thus the following scalar is Galois-equivariant and depends only on the covector:

    v(P,ζ) = (1/(2d)) ∑_(a=1)^4 ζ^a y(aP).

Over Q(√d) use (x_d,y_d)=(d x,d√d y) from E₁ to E_d. Thus v(P,ζ)=√d·U/2, where U is the same sum on E₁ without the 1/(2d) factor. Put h=ζ+ζ^−1, f=x(x−1)(x+3), R=y(2P₁)/y(P₁). Since 4P₁=−P₁ and 3P₁=−2P₁,

    h²+h−1=0,    U²=(h²−4)f(x)(1+hR)²,
    x(2P₁)=f'(x)²/(4f(x))−2−2x,   R=−1+f'(x)(x−x(2P₁))/(2f(x)).

The monic degree-12 polynomial H for U²/4 has descending coefficient vector

    [1, -700, -3842, 16695000, -224138925, -439425000, 1192371070500,
     -534340800000, -19638779315625, 501591411562500, 3056024037318750,
     19643523283125000, 101989511552503125].

The accompanying exact symbolic verifier forms the ordinary fifth division polynomial ψ₅=ψ₄ψ₂³−ψ₃³ of E₁, reduces the doubling expression modulo ψ₅, takes the norm over h and the resultant over x. The resulting **monic** polynomial is H², H is squarefree and nonzero at the origin. The two h choices and twelve x choices parametrize all the squared values above; the resultant has no roots from poles since f is invertible modulo ψ₅. Thus there are twelve distinct nonzero squared values, hence 24 distinct signed values since P↦−P negates the sum. There are exactly 24 covectors, so this scalar separates them. Consequently one can give K_d as

    Q[T] / ( d¹² H(T²/d) ).

For completeness this is a **field** for every such d, not a 24-factor product presented as one field: on E₁, Frobenius at 13 has trace −2 and determinant 13. Its characteristic polynomial over F₅ is irreducible (discriminant 2) and its image in F₂₅^×/F₅^× has order 6, as the supplied recurrence shows. It acts transitively on the six F₅-lines of V, and similarly on the dual lines. Quadratic twisting preserves the projective action even if 13|d. Moreover the scalar 3 from above generates F₅^× (its inverse does too on V^∨). Hence the whole Galois group acts transitively on the 24 covectors; their 24 distinct values have an irreducible minimal polynomial. The auxiliary field changes with d, even though its degree-12 square-coordinate subfield is fixed. A candidate bound on an unrelated class group would not satisfy this test.

Related general descent algorithms: [Schaefer–Stoll, How to do a p-descent on an elliptic curve](https://eref.uni-bayreuth.de/id/eprint/6228/). Their common point-algebra map uses Weil pairing to μ_p; the constant-coefficient covector injection and S-class-group upper bound above were proved directly. The only numerical replay in this packet verifies the universal polynomial and trace computations; the actual indexed class-group bound remains open.
