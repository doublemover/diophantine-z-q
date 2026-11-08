# Independent Serre open-image application review: active Version 13

## Decision and exact scope

**ACCEPT the bounded non-CM/open-image/twist-subgroup application.** The actual fixed curve E_l meets Serre’s hypotheses. Its rational 2-adic Tate representation, and every quadratic twist in the manuscript’s family, have the required nonidentity unipotent in the image of G_Qab. The same argument gives absolute irreducibility on the cyclotomic subgroup and no invariants after an abelian scalar coefficient extension.

This independently checks the source interface and its actual use in V13 lines 12642–12694. It does not accept all other Kato hypotheses, the entire K15 deduction, the restricted converse, the prime-pattern theorem, or the literal 318 construction. There is no new Lean formalization or compile.

The active manuscript is manuscripts/quartic_v13.tex, SHA256 9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd. The reviewer did not author its target passage. BINDINGS.json pins the actual curve, character family, rational and abelian-kernel consumers, retained-class continuation, and bibliography. The relevant historical V11 passages are byte-identical, but V13 is the current target.

## Published source and correction check

The freshly retrieved institutional PDF is the **published journal scan**, not an unverified author preprint. Its first article page visibly says Inventiones math. 15, 259–331 (1972), Springer-Verlag 1972. Both printed pp.259–260 were rendered and read. The file SHA256 is 93970ed93730194af8bed0f1f59d29cbed061d20f34f4bcffc079ad8aedf01d5, exactly the retained primary-source pin.

On p.259 the setup is an elliptic curve over a number field with no geometric complex multiplication. Assertion (1) bounds the indices of the finite torsion images. On p.260 assertions (2)–(3) express openness of the full adelic image. Assertion (4) explicitly gives openness of the l-adic image **for every prime l**. Serre identifies that fixed-prime assertion as already proved in his McGill course, Chapter IV; the new contribution of the article is the additional variation in l. Thus the source includes l=2 and does not require a surjective or irreducible mod-2 representation.

Kato’s original published 1999 article was also read at printed pp.317–318. Condition 0.6(ii) asks for an element in Gal(Qbar/Qab), not merely the cyclotomic subgroup. Example 0.6.2 explicitly states that the non-CM Tate image of that abelian kernel contains an open SL2 subgroup and derives the required one-dimensional fixed space. Its reference is **Serre [S4, Chapter IV]**, not literally the 1972 article. The elementary verification below explains why the checked 1972 openness statement suffices for exactly the same application; it does not misidentify Kato’s citation.

A bounded correction check used the official Serre bibliography and current Crossref metadata. Bibliography item [154] gives this article under 1972; the nearby “Correction” is attached to another paper, item [158]. Crossref agrees on volume, issue and pages but gives December 1971, unlike the visible journal heading and official bibliography. This is recorded as a metadata discrepancy, not a mathematical source change. Crossref returned no related update, and the bounded title/DOI correction search found no relevant correction. **This is not a guarantee that no correction exists.** No alternate version was substituted for the primary scan.

## The actual curve, not the CM index-generator curve

V13 lines 1885–1902 specify E_l: y²=x(x−l)(x+3l), for positive squarefree l congruent to 11 modulo 12. Its roots 0,l,−3l are distinct. Direct Weierstrass-invariant calculation gives c4=208l² and Delta=2304l⁶. Therefore

j = 208³/2304 = 35152/9.

The fraction is reduced and is not an integer. By the classical algebraic integrality of CM j-invariants, this excludes geometric complex multiplication. This is the same non-CM check already present in the retained A033 application; it has been recomputed here, not silently replaced by a generic non-CM assumption.

The point-generation curve over Q(sqrt(2)) has CM and is expressly distinguished in the manuscript. No open-image assertion about that curve is made here. E_l has full rational 2-torsion, so mod-2 surjectivity would be false. That does not contradict an open characteristic-zero 2-adic image.

V13 lines 12237–12276 fix E_l first, then T=T_2E_l and V=T tensor Q_2, and then introduce the family of quadratic characters. The open subgroup below may depend on E_l. It does not depend on the number or sizes of later conductor primes. No uniformity across different l is claimed.

## Explicit abelian-kernel verification

Choose n at least 2 such that H=rho_T(G_Q) contains 1+2^n M_2(Z_2). Write U(t)=[[1,t],[0,1]] and L(t)=[[1,0],[t,1]], and put D=diag(1+2^n,1). All three types of matrices used below are in H. With the commutator convention [A,B]=ABA^-1B^-1,

[D,U(2^n a)] = U(2^(2n) a),

[D,L(2^n a)] = L(−2^(2n) a/(1+2^n)).

Lift D and the relevant U or L to G_Q. Their group commutator lies in G_Qab, the kernel of the maximal abelian quotient. Hence rho_T(G_Qab) contains every upper and lower unipotent with parameter in 2^(2n)Z_2. This does not infer membership in G_Qab merely from membership in a cyclotomic kernel.

For completeness, these unipotents contain an open SL2 subgroup. If u is congruent to 1 modulo 2^(4n), set x=2^(2n) and y=(u−1)/x. The identity

U(x)L(y)U(−x/u)L(−yu) = diag(u,u^-1)

uses only parameters in 2^(2n)Z_2. For any g=[[a,b],[c,d]] in SL2(Z_2) congruent to I modulo 2^(4n), a is a unit and

g = L(c/a) diag(a,a^-1) U(b/a).

Thus rho_T(G_Qab) contains the principal SL2 congruence subgroup of depth 4n. These are finite products of actual commutators; no unproved linear-disjointness or Lie-algebra claim is required. The matrix identities were checked symbolically, and the subgroup argument was checked mathematically.

Every quadratic character is abelian, so χ restricts to 1 on G_Qab. Consequently **the identical subgroup** acts on Vχ for every character in the manuscript’s family. Because Q(mu_2∞)/Q is abelian, G_Qab is contained in G_Q(mu_2∞); the latter image contains the same subgroup.

Take nonzero b,c in 2^(2n)Z_2. U(b) has a one-dimensional fixed space over Q_2 and supplies Kato 0.6(ii). Its only invariant line over any algebraic extension is the first coordinate line; the only invariant line of L(c) is the second coordinate line. Thus the cyclotomic restriction is absolutely irreducible. This also proves irreducibility over G_Q, without any residual hypothesis.

If an additional scalar coefficient action is abelian, it is trivial on G_Qab. On Vχ tensor any Q_2 coefficient algebra, the equations for being fixed by U(b) and L(c) force both coordinates to vanish, since b,c are nonzero Q_2 scalars and therefore units. This verifies the fixed-vector assertion used at V13 lines 12663–12675 even when the scalar specialization is not finite order. The coefficient exact sequence, finiteness and Iwasawa-module arguments themselves are separate steps.

## Hypotheses not smuggled into this conclusion

- The argument is rational and away from 2. If b is a nonunit in Z_2, the cokernel of 1−U(b) on T has torsion. Kato’s stronger integral condition 0.6(ii_str) is **not** established or needed at the primes in the audited application.
- No residual irreducibility is inferred; the actual residual image here is trivial.
- The proof preserves the preselected real sign and local squareclasses: it works for all quadratic characters and adds no new local requirement. It does not prove that the character family was constructed with those properties.
- Purity, oddness, nonvanishing of the retained class, index-set coverage, norm identities, the exact coordinate ideal, and comparison of local cohomology conventions remain distinct obligations. Their explicit continuation is pinned so this input cannot be mistaken for an unrelated generic theorem.
- The retained A033 record also has other open-image consumers, such as the uniform ring-class torsion annihilator. Its existence and one earlier use are recorded, but this review does not newly accept every such consumer.

APPLICATION.json records all nine required/constructed/why-match/evidence obligations. This is an independent bounded acceptance of the actual Serre input, not bibliography-only acceptance and not a claim to have independently reproved Serre’s full theorem.
