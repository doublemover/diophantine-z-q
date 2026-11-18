# Choosing an actual scalar lift search: a fixed-field skew trace, and an exact denominator floor

For the distinguished fiber at the *unchanged* prepared b, let R=b/17, D=1−R, H=3D/R, β=[R] and θ=[D] the positive squarefree representatives. Assume θ>1. In the earlier marked Jacobian J: y²=x(x+4)(x−H), a lift of δ=(D,1,D) suffices for a literal nonzero pair there. Two exact tests avoid treating the large unknown squarefree complement as a numerical input. Neither decides global existence at the selected integer index.

**One particular point, not just a positive rank on another curve.** The quadratic R-twist of J has model J′: Y²=X(X+4R)(X−3D). Its rational point P=(4D,4D) has precisely the same split Kummer triple (D,1,D), because 4D+4R=4 and 4D−3D=D. P is non-torsion: the largest root has odd valuation at 3 since D is a 3-adic square unit; the two smaller roots have negative differences from larger ones. Thus there is no rational 4-torsion. The images of the roots at 0 and −4R have negative first class, the largest has first class 3D distinct from D, and O has trivial first class; odd torsion does not change Kummer classes.

Set K=Q(√R)=Q(√β), conjugation σ, and t:J′→J over K given by t(X,Y)=(X/R,Y/(R√R)). Then δ comes from J(Q) **if and only if**

    t(P) = U−σU    for some U in J(K).                            (1)

There is no unspecified 2-torsion correction. To see this take a geometric half H′ of P and use the canonical root-order identification J′[2]=J[2]. Its Kummer cocycle c_g=t(gH′−H′) takes values in that constant group. If S∈J(Q) has class δ, a geometric half A has exactly that cocycle (coboundaries of the constant 2-torsion module vanish). Then U=A+tH′ is K-rational, since the two corrections cancel over K. A lift of σ sends it to A−tH′ because t changes by a minus sign; hence (1). Conversely if (1) holds, S=U+σU is rational, and A=U−tH′ is a half of S. Over K its cocycle is c_g. At g restricting to σ, gA−A=σU−U+2tH′+c_g=c_g, so S has the precise marked triple. This argument also works for the local product algebra at split places or follows there directly from the surjective local difference map. Thus the global question is whether ONE explicit point is a skew trace over the fixed small-norm-definition field, not a request for a rank bound on a neighboring twist. For the actual scalar below the field is specified by the explicit β=204618888056724185, independently of the unexpanded θ. No local-global norm principle for the elliptic group is invoked.

**The actual scalar barrier.** Translate a lift by the rational root (0,0); it now has class (G,1,G) with [G]=[−3/R] because the root class is (−H,1,−H). Take the representative G=−3/R. The same partial isogeny computation as in ONE-SQUARE.md gives the equivalent single-variable condition

    w²=16v²+G(v²+H/G)²=16v²−(3/R)(v²−D)²,   v,w rational with v≠0.       (2)

Indeed for any class (G,1,G) write x=G h₁², x−H=G h₂², x+4=h₃²; taking v=h₁+h₂≠0 gives w=2v h₃. Conversely for a solution set V=Gv², x=(V+H)²/(4V), giving x−H=(V−H)²/(4V) and x+4=(w/(2v))². V+H and V−H cannot vanish for this negative G since D is positive nonsquare; a root representative would contradict the torsion exclusions for δ in the marked-Jacobian proof. Changing v's sign does not change (2).

For v=m/n>0 in lowest terms, at any p≥5 with k=v_p(R)>0 odd, necessarily v_p(v)=0. For v of positive valuation (v²−D) is a unit; at negative valuation the second term of (2) has valuation 4v_p(v)−k, smaller than the first and odd. Both cases preclude a square. For a unit, any 2v_p(v²−D)<k gives the same contradiction. Hence m²≡n² mod p^ceil(k/2). At the real place (2) gives |v²−D|≤4v√(R/3), or
    
    √(1+R/3)−2√(R/3) ≤ v ≤ √(1+R/3)+2√(R/3).

Thus |v−1|≤e for e=2√(R/3)+R/6.

Use the *actual* a=0 or −1 with h=328655617654071015360, g=1094218652709755, r=4g, A=114444r, J=h g⁸·11·17 and root label 1+6²¹·3⁶⁵⁵³⁶J. The source gives R=A W²/(17(1+A)²), W=N²+rQ², N=1+(H₀/r)²+2J₀/r, Q=c/(H₀r¹⁵), 0≤J₀≤1, 1/100<|H₀|≤1 and |c|<1. Consequently W≤(1+r⁻²+2/r)²+10000/r²⁹. At this same scalar the earlier two finite verifications give D≡6 mod7 and odd positive v_p(R) for all eight primes p|β. The would-be v=1 requires 16−3R=13+3D≡3 mod7 to be square, impossible. Therefore m²−n² is a nonzero multiple of β. The exact rational inequalities checked by verify.py show e<1.25131411×10^−11 and
    
    β ≤ |m²−n²| ≤ e(2+e)n²  ⇒   n>90,422,000,000,000.

This is a height floor in the *specific* negative isogeny coordinate at those indexed scalar choices, not a height bound on an arbitrary original witness, a proof of nonexistence, or a statement about all common indices. It explains why a modest rational search in this chart cannot decide the global lift. The known local Selmer and restricted-support results supply neither (1) nor an infinite descent on (2). No change to the four open original realization hypotheses.

Dependencies: forward-distinguished-pole-jacobian-r1/README.md 382ac431a5e6002eb10c36949b3305adc8df1ec4c8ad30344a0d7ef92e1f268c, ONE-SQUARE.md 392f99a7bfeb9ab6611fbe42bfa17577c41e9df2fc4bfa7d63592df73a19c62f; indexed constructor db5260f3 and indexed-free-rank-one manifest f4578f72. At source pin a0950ac7c24df6d336a196966fb790d6abd55e44, forward-actual-ambient-primitive-lifts-r1/ScalarActualInputs318.lean blob 9b4eda0b and ActualScalarRoot318.lean b6539423 give common_bounds and inverseNorm_bound; the h enclosure is in the indexed constructor. Source mathematics, not Lean.
