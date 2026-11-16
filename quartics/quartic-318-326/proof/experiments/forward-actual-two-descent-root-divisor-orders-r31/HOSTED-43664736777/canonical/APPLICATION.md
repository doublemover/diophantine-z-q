# Actual two/three-adic preparation witness exposure

Own descent21 and weighted21, run43664736777, HEAD1785ba5569eff8aebbd69b9236dead5e0fcc3c02. Source-only candidate; no local Lean.

1. Inputs: original arbitrary integer a, four integer labels, integer h≠0, label1≠0,1. At2 retain exact depth padicValInt2 h+15≤padicValInt2(label1−1). At3 retain Even h, Even(label1−1), and strict3-adic depth. No extra premise.
2. Constructed conclusion: same original packed W witness has rational valuation zero at2 or3. No target predicate is supplied as input and no replacement witness is constructed.
3. Domain: full original DetectorGateWitness318.witness (a:ℚ) labels h, including all existing gates and all integer labels, with translated index label1−1.
4. Maps: same gates0,33,37; expose local let w immediately before each native detector33/detector37 rewrite. This unfolds only the existing abbreviation to the same witness; original normCoefficient(chartU h) and real half-trace remain exact.
5. Arithmetic: same native valuation products, half-trace valuation equalities/lower bound and inputR orders. Add typed hself:padicValRat2(2:ℚ)=1 from native padicValRat.self(p:=2), normalizing only the natural-number cast. Existing prime Fact instances2,3,17 are unchanged. No altered sign, denominator, offset15 or norm identity.
6. Consumers: unchanged ScalarPackedLocalUnit318.actual_unit with same hr,hf,hH,hn,hn1, its exact inequalities and output .2. Integer input multipliers and unit_three valuation of2 remain unchanged.
7. Exceptional cases: h=0 and label1=0,1 remain excluded by original hypotheses; all other permitted integers, signs and parity boundaries retained. No positivity premise or enumeration added.
8. Own verification: both RESULT packet hashes equal their own current intake and both before bytes coincide. HalfTraceDepth passes2.019s descent and1.669s weighted. TwoThree fails2.170s descent and1.671s weighted after105 successful commands. Actual errors are eight rewrites under local w and one untyped rational prime self rewrite. No downstream pass asserted.
9. Delta/boundary: eight explicit local-w unfoldings and one typed native valuation fact; all public signatures, imports, options and original assumptions unchanged. Independent source review, future all-copy propagation and hosted kernel verification remain separate. No resource/trust changes or Lean acceptance claimed.
