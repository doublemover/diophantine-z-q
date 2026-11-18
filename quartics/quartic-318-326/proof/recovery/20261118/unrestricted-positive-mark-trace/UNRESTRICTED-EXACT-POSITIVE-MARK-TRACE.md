# One rational trace test equivalent to the unrestricted marked realization

Fix any true prepared pole, including each of the four at the same source index. Let B=17b=βv², V=B²(1−b/17)=θ(Bz)² as usual, β,θ positive squarefree, 17|β. Assume θ>1, as θ=1 is directly soluble. The gain parameter is free. A literal pair requires rational points on E_n and E_(nθ) with common first abscissa squareclass β and nonzero abscissas, where E_m:y²=x(x−m)(x+3m); the other two Kummer coordinate classes need NOT agree, and zero ordinates are allowed. Equivalence with the literal fixed abscissas uses the ordinary common square rescaling B/x(first) and the second square factor V/θ. The theorem below imposes no other equality of marks.

**Criterion.** The original pair exists over Q if and only if there are a,b1,s,w,h in Q with b1 s h nonzero, w>0, and, writing θ>1 fixed,
     
     N = a²−θ b1²,         s² = N+4a+4,
     w² = (N−12)²+48a²,    β h²=6(w+12−N).

Here w is the POSITIVE square root, not a free sign. If one requires both ordinates nonzero, add the open test that neither of the reconstructed rational points below has zero ordinate. This criterion applies to fixed indexed scalar as well as contacts and does not solve the equations there. In contrast with the aligned-full-mark trace, the key isogeny below uses only the first abscissa character. It gives a particular elementary candidate for attacking the main unresolved step with one quadric and one residual square; no assertion of rationality of the associated surface.

**Forward from a literal pair.** Work over K=Q(√θ) with conjugation σ. For the root T0=(0,0), let φ:E_n→E'_n be the quotient, with dual ψ, where
     
     E'_n:y²=x(x²−4n x+16n²),
     x(φP)=x(P)+2n−3n²/x(P).

The ψ-Kummer character of S∈E_n(Q) at x(S)≠0 is exactly [x(S)]. For example x(ψH)=(y(H)/(2x(H)))² and translation by T0' changes the sign of y(H)/x(H); the kernel of ψ is rational T0'. Take ψ-preimages H1 and H2 of the two given rational points S,T on E_n,E_(nθ) with [x]=β. Their Galois cocycles agree literally, since the constant rational kernel has no coboundaries. Transport the second point group to E'_n over K by dividing coordinates by θ and θ√θ; denote transport by j. Then R=H1+jH2 is in E'_n(K). An extension of σ gives σR=H1−jH2: the two same corrections cancel because they are 2-torsion. Thus R+σR=φS and R−σR=jφT. Neither is O since S,T have nonzero abscissas. Hence x(R) is finite and nonrational (otherwise σR=±R). Set Z=x(R)/n−2=a+b1√θ. The chord through R,σR has rational intercept l at x=0. For distinct abscissas, substitution into the cubic gives x(R+σR) N_K(x(R))=l². Since x(φS)=y(S)²/x(S)² is square if y(S)≠0, N_K(Z+2) is then a nonzero rational square. If instead φS=T0', l=0 and this quotient would be 0/0; the group homomorphism E'_n(K)→K×/K×² given by the first abscissa (using derivative at T0') also gives the rational norm-square identity as follows: when the chord has intercept zero, divide by x in the cubic to obtain x(R)x(σR)=16n², itself a square. This accounts for a first zero ordinate without excluding it. Since Z is nonrational, Z²+12 and Z+2 are nonzero. The equation of R implies (Z+2)(Z²+12) in n K×², so N_K(Z²+12) also is a rational square. The positive root w of this last norm has square (N−12)²+48a², N=N_K Z.

**One explicit mark, including its sign.** Put A=a²+θb1²+12, d=2(A+w)>0, U=(Z²+12+w)/d. Directly dU²=Z²+12 and d N_K U=w. For any nonrational Z satisfying the two norm-square tests, choose c∈Q× and H∈K× such that Z+2=cH²: for norm s² take c=2(a+2±s), H=(Z+2±s)/c, using a nonzero c. Set n=c/d. In the forward direction we may instead take n to be the ORIGINAL given parameter and c=nd because the equation of the existing R makes (Z+2)/(nd) a square in K. Consider the degree-four étale algebra
     
     L=Q[√θ,r],   r²=d,

as the tensor product of two independent quadratic algebras, even if d or dθ is a rational square. Its commuting automorphisms σ,τ change the signs of √θ,r respectively, fixing the other formal generator. The common fixed ring is Q and its τ-fixed ring is K. Every formula below is componentwise valid in this algebra including its split cases. Put
     
     X=(Z+rU)/2,   γ=X r H,   P=(nX,n²γ).

Then τX=−3/X and X−3/X=Z. Consequently X(X−1)(X+3)=nγ², P∈E_n(L), and τP=P+T0 by the explicit torsion translation (x,y)↦(−3n²/x,3n²y/x²). Throughout X is invertible. The points P+σP and P−σP therefore lie in E_n(K) and are respectively invariant and anti-invariant under σ; the latter transports back to E_(nθ)(Q). Their abscissas are nonzero as verified below. Also φP has x-coordinate n(Z+2), the same as R in the forward direction, and thus φP=±R there: φP∈E'_n(K) by τ-invariance, so even in the split case there is a single sign over the field K. The two recovered points consequently are independently ± a φ-preimage of each original trace φS or φT. Each fiber is a pair differing by T0, whose two abscissas have product −3n² (or −3(nθ)²); this is true also at nonzero 2-torsion. Thus the POSITIVE abscissa in each fiber is unambiguous up to the harmless sign of the point.

For explicit computation let
     
     J=(X−σX)²/(X σX)=X/(σX)+σX/X−2=(w−N−12)/6.

Indeed (X)⁻¹=(rU−Z)/6, so the expression is σ- and τ-invariant. We have w²−(N+12)²=48θ b1²>0, hence J>0. In particular the denominator X−σX is invertible everywhere. Intersecting the lines through P,σP and P,−σP with the cubic as in the chord argument gives respectively the two rational abscissas (the second after twisting):
     
     x₁=n²d(H−σH)²/J,    x₂=θ n²d(H+σH)²/J.

These are positive and nonzero, since Z+2=cH² nonrational forces both H±σH nonzero. Their ratio is a rational square, and their common squareclass is [θdJ], because H−σH has the form √θ times a rational. Substituting d,J and w² gives the exact identity
     
     θ d J = (θ b1/3)²·6(w+12−N).

This proves the last mark test in the forward direction, without having to follow a secondary mark; positivity gives the original β rather than −3β. Conversely these rational points immediately realize the common class β if the last test is satisfied. For their literal normalization, if x₁=Bt² and x₂=Bv1², take the free parameter n/t²; its V-twist differs from nθ by (Bz/t)², so the second abscissa becomes B(v1 Bz/t)². All scalings/ordinates are rational.

**An elementary two-quadric search form.** Equivalently, choose c0≠0 rational, r0=β c0², r0>1 and a,b1,s∈Q with b1s≠0 such that
     
     θ b1²=(r0−1)(12+a²/r0),
     s²=(a+2r0)²/r0+16(1−r0).

To see both directions, set r0=β(h/12)², giving w+12−N=24r0. From (w+12−N)(w−12+N)=48a² obtain N=12(1−r0)+a²/r0 and w=12r0+a²/r0>0. The remaining equations follow, and conversely reproduce the positive w and h=12c0. This search form has no separate twist n, θ-extension coordinates, equality of auxiliary full marks, conductor/point order hypothesis, or unproved low-corank converse. Setting a=2r0 makes s²=16 and specializes to θ b1²=4(r0−1)(r0+3), only the familiar positive anchor; this restricted genus-one condition is NOT necessary for the full test. The two-quadric description for fixed c0 is a varying genus-one intersection in general, not two independently soluble conics. Actual rational c0,a,b1,s at the four linked poles remain open.

Paper proof using the usual split 2-isogeny and dual, with exact rational replay, not Lean elaboration.
