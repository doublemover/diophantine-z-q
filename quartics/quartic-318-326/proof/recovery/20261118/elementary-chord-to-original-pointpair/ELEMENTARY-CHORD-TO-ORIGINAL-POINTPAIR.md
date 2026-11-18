# The unrestricted positive-mark trace test is just the rational chord of one conic

This is a separate elementary proof of the preceding exact unrestricted equivalence, with explicit rational candidates and a source-only Lean adapter to the literal PointPair rather than two independently marked or hypothetical twists.

For the actual positive squarefree nonsquares β,θ write B=17b=βv², 1−b/17=θz², V=B²θz². In the square-complement case θ=1 use the previously verified equal-gain construction. For θ>1, the precise original two ordinate equations normalize to distinct nonzero gains e,f with
     
     Y²=β(1−e)(1+3e),  Z²=β(1−f)(1+3f),  ef=θw²,  w≠0.

Indeed start from η,S,y₁,y₂ at abscissas B,BS², put e=η/B, f=ηV/(BS²), Y=y₁/(Bv), Z=y₂/(BvS³), w=eBz/S. A zero e would force β square, and equality e=f would force θ square. Conversely η=Be, S=eBz/w, y₁=BvY, y₂=BvS³Z give the literal data, including zero ordinates if they occur. Every denominator is nonzero.

Draw the unique rational line Y=d+m e through the two conic points. Writing d=βc and m=−βk/2 gives their quadratic
     
     A e²−2C e+F=0,   A=12+βk²>0, C=4+2βck, F=4(βc²−1).

This equation is the original conic after multiplying the difference of its sides by 4/β. Vieta and the square discriminant now give exactly
     
     θu²=(βc²−1)(12+βk²),       s²=16+β(k−2c)(k+6c),

with u=Aw/2, s=A(e−f)/4 both nonzero. Conversely use e,f=(C±2s)/A, w=2u/A, Y=βc−βke/2, Z=βc−βkf/2. These rational formulas need no Galois descent, no square root in a number field, and no group cohomology. If θ>0 the first equation forces r=βc²>1, so this is the previous two-quadric trace test after a=βck, not a more permissive surrogate. Finite candidate certificates can now be checked on the actual b using only rational arithmetic operations. Neither cofactor θ nor r need be factored for substituting a candidate. This does not produce four candidates from the common source.

RationalGainChord318.lean contains the core bidirectional conic argument. ActualRationalGainChord318.lean wraps the core in the actual imported NormalizedPolePoints318.PointPair, from pinned original module SHA256 410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542, Git a0950ac7. These drafts were not locally compiled.
