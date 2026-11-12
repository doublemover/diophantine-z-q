# Explicit exponents instead of an assumed decay implication

## Fixed scale and exact domain conditions
Take N=n^8, B=n^32 and delta=1/64, with n>=2. Then N>0, B>=1 and (N+1)^3<=(2n^8)^3=8n^24<=n^32. The actual reduced-Dirichlet order is exactly ceil(B²/N)=n^56, because B²/N=n^56 is an integer. The canonical integer radius H=toNat(ceil(RB)) is the same original support radius, and H<=(R+1)n^32. Put A=R+1 and J=2A+1, giving 2H+1<=J n^32.

## Expanded kernel polynomial bound
The r17 budget has four terms 32|c|H(2H+1)/N, 32|c|H(1+log Q), 4(2H+1), 4Q(1+log Q). Native log_pow and log_le_sub_one_of_pos give 1+log(n^56)<=57n. Before the common n^58 enlargement, the respective terms have degrees 56,33,32,57. All constants are retained in
D(c,A)=32|c|A(2A+1)+1824|c|A+4(2A+1)+228.
Thus the complete budget is <=D n^58, and its real square root is <=sqrt(D)n^29. Nonnegative factors and monotonicity are explicit. No logarithmic factor is silently declared bounded.

## Exact fixed divisor loss and moment degree
The genuine fourth-moment budget is (2H+1)^2*(2 divisorConstant(delta)*(H²)^delta+4). Since H²<=A² n^64, fixed delta=1/64 yields (H²)^delta<=(A²)^delta*n. This is native real-power algebra with nonnegative bases, not a numerical root approximation and not a scale-dependent choice of delta. Its constant is chosen before n. Therefore momentBudget<=E(A)n^65 where E=(2A+1)^2*(2 divisorConstant(1/64)*(A²)^(1/64)+4).

## Actual full integral and original normalization
Apply the r18 literal full nonseparable smooth minorArcIntegral estimate with the same N,B,H,delta. Its W-dependent radius and mixed constant precede n. Multiply sqrt-kernel degree29 and moment degree65 to obtain degree94. Absorb C*(2R+3)^5*sqrt(D)*E into one K>=0. The original complex denominator is (B:complex)^3, whose norm is B³=n^96, so the normalized norm is <=K/n² by exact division. No remainder has been redefined.

For the sequence n+2 every bound holds at every stage. The natural cast tends to infinity, its reciprocal square tends to zero, and multiplication by fixed K preserves that limit. Native squeeze_zero_norm proves the actual complex normalized minor integral tends to zero. Separate growth lemmas show both N and B grow and the original geometric separation condition holds on precisely this sequence.

## Common-scale audit against the old major argument
Read ActualOriginalArcDiagonal, ActualOriginalFiniteMajorArcError and the exact major/minor decomposition. The old stageScale A n=(n+1)^3*(1+A n) depends on A n=C(1+n)^k(2n)latticeSixthMass*finiteArcMass. Its major result does not bound its growth above, so it cannot simply be substituted into a fixed-delta minor estimate: B^(2delta) can defeat the cutoff saving. Conversely, no bound here proves the old major error small at B=N^4 for arbitrary derivative exponent k.

This packet therefore proves a real new minor-only normalized decay theorem, but NOT simultaneous major+minor convergence. The next concrete bridge is to bound the literal finiteArcMass<=sqrt(32kappa)N^6 and parameterize B=n^(8p+32), delta=1/(16p+64), choosing p from the old fixed derivative exponent. That route is identified, not claimed accomplished in these five modules. Final count/prime/ray/order/Anchor/rank conclusions remain open.
