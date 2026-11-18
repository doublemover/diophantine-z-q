# Four odd 2-valuations: an integral exchange of the last branch and infinity

Consider the original four-root twist X_q (the true normalization of the parameter P¹_Z). Suppose **all four** q_i have odd 2-adic valuation and the signed odd unit parts of q₀,q₁,q₂ are congruent to one another modulo 4 after removing powers of 2. There is no congruence condition on the unit part of q₃. Then the original X_q has an explicit proper birational modification, flat proper regular over all Z. This is *not* the case of three odd squarefree representatives and a fourth even representative: now all four squarefree representatives are even. We use an automorphism of the dyadic parameter line, not a nonintegral rescaling.

On a neighbourhood of 2 invert the odd integer M=375·343 and use
    t=375T/(T+343).
Its matrix has determinant M, and thus is genuinely in PGL₂ there, including at T=−343 and infinity. For i=0,1,2 put y_i=r_i/r₃ and y₃=1/r₃. Then there are exact rational identities
    y_i²=q'_i(t−c_i),  q'_i=(q_i/q₃)(343+b_i)/M,   c_i=375b_i/(343+b_i);
    y₃²=q'₃(t−375),   q'₃=−1/(M q₃).
Conversely recover r₃=1/y₃, r_i=y_i/y₃, T=343t/(375−t) in the common generic field. The branch tuple is now
    c=(0,32,1120/3,375).
All denominators used are odd. In particular the new cluster ratio K=c₂/c₁=35/3, K−1=32/3, 2K−1=67/3. These are NOT the old constants 2401,2400,4801. For each parameter affine, a field isomorphism over this parameter automorphism identifies its integral closure with that on the inverse affine. This gives isomorphic *projective* normalizations with their parameter actions transported; it is not necessary to equate the original finite chart with an entire new finite chart.

The q'₀,q'₁,q'₂ have even valuation and their unit parts all agree modulo 4: each 343+b_i≡3 mod4 and the other factors besides q_i are common. The valuation of q'₃ is odd. Thus after taking dyadically unramified scalar square roots of coefficient ratios, this transformed family is the one with **new contacts** c and q'⁰=(d,d,d,2a), d,a∈{±1}. The following details recheck its dyadic construction; the bound result for the old contact tuple does not by itself justify changing it.

Let D=Z_(2). For the new pattern take u=y₀, h=(y₁−u)/2, k=(y₂−u)/2,w=y₃, f=a(d u²−375). The finite equations are
    t=d u²,  h²+uh=−8d, k²+uk=−8dK,  w²=2f.
On the usual restricted reciprocal neighbourhood x=1/u, s=1/t=d x², divide h,k,w by u, getting the standard two monics with right sides −8d x²,−8dKx² and W²=2a(d−375x²). The monic rank, generic field comparison, exact overlap, complete intersection S₂ and R₁ are as follows: in characteristic zero contacts are distinct, finite simple-branch charts smooth; at dyadic u≠0,1 the first two adjunctions are étale, the last equation has linear parameter 2 times a unit in the regular ambient; infinity x=0 is regular by the same 2 test. Possible bad points have codimension two, one at u=0 and four at u=1, by finite flatness over D[u]. Thus these are actual normal finite rings. Intersection with the fixed field again gives these same invariant rings upstairs for the semilinear group of the splitting scalar extension; no wild quotient smoothness principle is used.

At u=1 put v=u−1, m=1 if d=1 and m=0 if d=−1, W'=w−2m. Define c₁=(a(d−375)−2m²)/4∈Z: d−375 is 2 modulo 4 for d=1, zero for d=−1. The exact equation is
    W'²+4mW'=2ad v²+4ad v+8c₁.
Thus the ordinary reduced (2,v,W') blowup, pulled back under the two étale monics, has exactly the saturated charts of RAMIFIED-DYADIC-DD2 §1 with this c₁. The 2-chart has Y²=2(ad(V²+V)+c₁−mY), over residual V²+V+c₁=0 one gets étale copies of the standard node (derivative 1 mod2). The v-chart has 2=vQ, Z²=vQ(ad+adQ+c₁Q²−mQZ); its extra Q=0 origin has smooth tangent conic Z²=vQ. The second reduced union blowup resolves all these points at every label. In particular no assertion that the two Artin–Schreier roots are both rational is needed.

At u=0 (where f is a unit and 2=w²/f), the three ordinary w,S chart preparations of the bound baseline apply with K in place of 2401: at n=0,1,2,3 set u=wⁿS,h=wⁿA,k=wⁿB, with f=f₀+ad w^(2n) S², f₀=−375a. The right sides of A²+SA,B²+SB are −d w^(6−2n)/f³ and K times it. Since K is a unit with residue 1, the coverage (initial w,S suffice), saturation (scale,2 times unit, two independent monics regular sequence) and exceptional-divisor regularity are identical: S direction has derivative-one monics; w direction S≠0 étale; the only remaining origins are zero at n=1,2 and A=B=1 at n=3. At n=3 set G=−d/f³, p=A−1. C obtained omitting B is regular with parameters w,p since C/(w)=F₂[A,A⁻¹]. Write j=B/A−1 and e=j−(K−1). Eliminating S from A²+SA=G gives
    j²+(1+G/A²)j−(K−1)G/A²=0,
    e(e+t')=−K(K−1)=H w¹⁰,   t'=D₁+G/A², D₁=2K−1=67/3, H=−K/(3f⁵).
This second equality uses K−1=32/3 and 2=w²/f. The exact exponent ten and coefficient are rederived, not inherited.

Put c₀=(D₁−d/f₀³)/2, D₀=(d/f₀³−d/f³)/w⁶. The numerator satisfies
    A²t'=2c₀+w⁶D₀+D₁(2p+p²).
D₀ is regular by the difference of cubes and c₀∈D (unit or even). Blow up (w,p) and normalize as in RAMIFIED-DYADIC-DD2, locally adjoining E=e/b² for scale b=w or p. Since t'∈(w,p)², the new equation
    E(E+t'/b²)=H w¹⁰/b⁴
is well defined, monic free on the regular base blowup chart, and shares the original fraction field. At p-direction w/p=0 it is étale (coefficient 1 mod scale). On the w chart p=wP:
    T₁=t'/w²=(c₀/f+w⁴D₀+D₁(wP/f+P²))/(1+wP)²,  E(E+T₁)=H w⁶.
If da=−1 then c₀ is odd: D₁≡1 mod8, f₀≡a mod8, so D₁−d/f₀³≡2 mod8 in this case. T₁ mod w=1+P². At P=1, z=P−1, its linear part is w, by the wP/f term and 2∈(w²); in the DVR modulo E,E+T₁ the order of w is exactly two by length two of the further quotient z²=0. Thus E,E+T₁,z are regular ambient parameters, and the two crossing blowups give exponent 8 and the following four finish with the smooth conic. The linear side charts and scale saturation are those of the bound proof for this exact transverse form.

If da=+1 then c₀/2 is even (same mod8 check), T₁ modulo w is P². At the sole exceptional point P=E=w=0 blow up the second nonreduced ideal (w,P) and normalize by E₂=E/b². At P-direction w/P=0 the coefficient again reduces to 1. At w-direction P=wQ the exact equation is
    E₂(E₂+T₂)=H w²,
    T₂=((c₀/2)/f²+w²D₀+D₁(Q/f+Q²))/(1+w²Q)² .
Modulo w this is Q²+Q; derivative 1. Thus at Q=0,1 the ambient parameters are E₂,E₂+T₂,w, with equation EV=unit·w², resolved in one ordinary blowup of the two reduced origins. All remaining directions are étale. At both normalized steps monic freeness gives injectivity after scale inversion, complete intersection over a regular base gives S₂, and any bad exceptional point just identified is closed codimension two, proving R₁ even before its next resolution. This identifies the actual finite normalization, not a merely birational equation.

The deck signs preserve the nonreduced first ideal since S=A⁻¹−A mod w; on its w chart the exact replacement for the second ideal is S=A(t'−2K). Since 2K is divisible by 2 and t'=w²T₁, S/w∈(w), so P'=±P plus multiples of w under the sign change of A (with half-gap integer) and of w. Hence the second ideal is stable as well. The remaining reduced centers are stable unions or unique nonregular successors. Over a genuine base neighbourhood of 2 choose the maximal-order étale cover splitting the q'/q'⁰ ratios, form the descended ideals and compatible finite normalizations successively (étale normalization and flat-local blowups), and use étale descent of regularity. The PGL₂ isomorphism transfers all modifications back to the actual X_q near 2, **over the original parameter action** by composing with its inverse. On the intersection with the established D(2) model remove the finitely many odd coefficient/contact/ramification/modification primes: both restrictions identify with the unchanged X_q. This gives the asserted proper model, flat by torsion-free integrality, on all Z. Example q=(2,10,−6,6) has first three signed odd parts 1,5,−3 all congruent to 1; its fourth sign need not match. Neither unequal first-three odd parts nor mixed first-three valuations are implied. No local Lean, minimality or final Diophantine theorem.

Primary references: [Serre normality criterion](https://stacks.math.columbia.edu/tag/031S), [normalization is étale-local](https://stacks.math.columbia.edu/tag/0ABP), [flat-local blowups](https://stacks.math.columbia.edu/tag/0805).
