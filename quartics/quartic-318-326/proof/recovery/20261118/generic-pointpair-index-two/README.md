# The unrestricted generic scalar PointPair has index exactly two

There is no rational-function PointPair at the generic source scalar pole, even if BOTH free twists and ALL Kummer marks vary. More strongly, no point exists over any finite extension of odd degree of its function field. On the other hand an explicit degree-two extension gives a point with both ordinates nonzero. Here “index” is the gcd of the degrees of closed points of this algebraic variety, or equivalently of its finite splitting degrees, not the integer index h of a multiple on the source curve. This settles the generic two-independent-slot section question left open in the preceding scalar and relative-mark packets. It does NOT say there is no rational PointPair after numerical specialization: reviewed rational specializations are known.

## A mod-four invariant on curves

Let k be ANY characteristic-zero field, with β and −3β both nonsquares, β nonzero. Let C/k be a smooth projective geometrically integral curve, with t∈k(C) nonconstant of odd degree as a map to the t-line. Put D=1−βt². We show that one cannot have normalized gains e₁,e₂∈k(C)× with

     Yᵢ²=β(1−eᵢ)(1+3eᵢ),             [e₁e₂]=[D].

The gains can be arbitrary rational functions, with no assumed amplitude, marking, or relation between their ordinates other than the equations. For f nonzero let O(f) be the finite set of GEOMETRIC points of C where the valuation is odd; poles count in the same way as zeros. Only the squareclass matters. Its cardinality is equivalently the sum of the residue degrees of the odd closed points. A constant function has empty O.

If e≠1, let s=Y/(1−e). Solving gives
     e=(s²−β)/(s²+3β).
The denominator cannot vanish because −3β is nonsquare and k is algebraically closed in k(C). The case e=1 has empty O, as does every constant s, including e=−1/3 with zero ordinate. If s is nonconstant of degree m, there are four distinct branch values to count: ±√β for zeros and ±√−3β for poles of the target rational function. At s=∞ the gain is a unit and gives no contribution. Above any ONE target geometric value the number of preimages of odd local degree is congruent to m modulo 2, since the sum of all local degrees in that fiber equals m. A conjugate pair of target values has the SAME number of odd preimages in each fiber, as s and C are defined over k and the conjugating automorphism bijects the fibers. Thus each pair contributes 2m modulo 4. The four values in two pairs contribute
     |O(e)| ≡ 0 mod 4.
This holds even when the two quadratic extensions defining the respective pairs are equal, provided both pairs are nonsplit and distinct as sets.

In contrast, for D=1−βt² the two target values ±1/√β form one nonsplit pair; its pole has even order. Hence
     |O(D)| ≡ 2 deg(t) ≡ 2 mod 4.
Furthermore EVERY closed orbit in O(D) has even degree over k, since its residue field contains √β (the value of t gives a root of X²−1/β). Suppose [e₁e₂]=[D]. Then O(D) is the symmetric difference of O(e₁) and O(e₂). Both differences O(e₁) minus O(e₂) and O(e₂) minus O(e₁) are Galois stable, so the second of them in particular has even cardinality as a union of even orbits of O(D). It follows that
     |O(D)| ≡ |O(e₁)|−|O(e₂)| ≡ 0 mod 4.
Contradiction. For C=P¹ and deg t=1, the contradiction is especially simple: precisely two conjugate places are in the symmetric difference, necessarily both in the same difference direction.

## The literal rational-functions source, at every integer input

Fix any integer a and legal fixed integer label n≠0,1. The formulas and six original Git source hashes are in the independently reviewed forward-scalar-subsystem-sections-r1/README.md, pinned in ORIGINALS.json. Use d=inputR(a)>10, d≡5 mod17, A=114444d=102²·11d. In the field F=Q(N,Q) of the original two independent common slots the exact map is
     W=N²+dQ²,     b=A(W/(1+A))²,     B=17b=βu²,
     t=u/17,       D=1−βt²=1−b/17,    V=B²D.
Here β is the positive squarefree representative of 17A, [β/d]=[187], v17(β)=1, and u=c₀W for a fixed nonzero rational c₀. In particular no input-dependent prime order or conjectural rank/Sha claim enters. These are the free common slots, not a chosen common integer multiple h.

In any odd-degree extension E/F a literal PointPair with parameter η and scale S≠0 would give e₁=η/B, e₂=ηV/(BS²). The ordinates divided by βu³ and β(uS)³ satisfy the normalized gain equations; [e₁e₂]=[D]. A zero gain would force β to become square by the first equation, impossible in an odd-degree extension of F. A zero ordinate was not excluded in the mod-four lemma.

Adjoin k₀=Q(√−d) to the constants. The degree of E k₀/F k₀ is still odd: F k₀/F is quadratic and linearly disjoint from an odd-degree E, or simply use the degree tower. The positive nonsquare β stays nonsquare over this imaginary quadratic field. Also −3β stays nonsquare because [3β/d]=[561] is nonsquare over Q. The split quadratic norm coordinates X=N+√−d Q and W/X=N−√−d Q give
     F k₀=k₀(X)(t).
View the finite odd extension E k₀ as a curve function field over k₀(X), by taking the projective normalization of the t-line. The full algebraic field of constants k in E k₀ over k₀(X) is a finite extension of odd degree: [k:k₀(X)] divides the odd total degree since k(t)/k₀(X)(t) has this same degree. Thus β and −3β both remain nonsquares in k. In characteristic zero this normalization over the full constants is a smooth projective geometrically integral curve (equivalently take its smooth complete model). Its degree over k(t) is odd. Apply the preceding mod-four result. This precludes all odd-degree finite extensions, including F itself.

## Sharpness and universal parameter

The function D is nonsquare in F: over k₀(X)(t) it has simple geometric zeros. The quadratic extension F(√D) gives explicit data with both ordinates nonzero: take
     e=(1−β)/(1+3β),  η=B e,  S=B√D,
     y₁=4β²u³/(1+3β),  y₂=S³ y₁.
Indeed β(1−e)(1+3e)=(4β/(1+3β))² and V=S². It follows that the unrestricted original PointPair variety, and also its open with both ordinates nonzero, have index EXACTLY TWO. In particular an odd-degree algebraic family of generic choices cannot replace a rational formula.

There is an additional one-parameter consequence: for b itself indeterminate over Q, the same literal variety over Q(b) likewise has index two. Make an auxiliary substitution b=17 βt² (e.g. β=17), so B=β(17t)²,D=1−βt² over Q(t). This is a quadratic extension of Q(b), disjoint from any odd-degree splitting extension; the composite over Q(t) still has odd degree. Take full curve constants (of odd degree) and apply the same lemma. Conversely over Q(b)(√D) one can use the same explicit construction with β=B,u=1 (the identity is algebraic even when β is not constant). S=B√D and both ordinates are nonzero. This one-parameter consequence does not replace the original two-independent-slot argument, whose base change in general could invalidate generic obstructions.

**Limits.** A rational section of any of these function fields would specialize in an open set, hence would have been a convenient uniform solution. The converse is false: rational points can exist on many, or even all members of a restricted arithmetic family without a rational-function section. The proof does not refute any actual fixed integer input, any fixed rational b, or the target diophantine theorem. It gives no statement about arbitrary even-degree extensions beyond the one exhibited, or about the infinitely correlated locus parametrized by actual integer multiples h. No Lean elaboration.
