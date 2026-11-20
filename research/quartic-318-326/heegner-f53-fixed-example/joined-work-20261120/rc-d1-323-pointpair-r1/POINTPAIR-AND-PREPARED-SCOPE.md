# Exact E323 marked point, equal-twist pair, and original producer scope

## One actual rational rank and mark, not a uniform source

For the original cubic E323: y²=x(x−323)(x+969), set

    x = 9226753553/5973136
    y = 1005467646233175/14598344384
    r = 23297/2444, u = 29719/2444, v = 85425/2444.

The literal identities are x=17r², x+969=17u², x−323=v²,
y=17ruv. All five numbers are strictly positive. In the original
ordered (x+3n,x−n) convention this gives an actual
`ActualTwoDescentPointExtraction318.KummerPoint 17 323`;
this is not merely an unmarked rational point or a signed rank
calculation. Its `KummerPoint.squareclass` root is exactly r since
y/(17uv)=r.

Good reduction at 5 and 53 is immediate from
Δ=2304·323⁶. The curves at these primes have 4 and 52 points
respectively. The given P reduces to (3,0) mod 5 and (1,25) mod 53.
The latter satisfies [224]P=(42,42)≠O and [13](42,42)=O in F53;
its image has order divisible by 13. If P were torsion its order
would therefore be divisible by 13. Its nonzero 13-primary subgroup
would inject at good 5 (prime-to-5 torsion injectivity), contradicting
4. Thus this exact rational point is non-torsion, independently of
the Heegner numerical trace, Selmer parity, or any rank conjecture.
The finite arithmetic script repeats both residue counts and sums.

## One exact equal-twist PointPair and certificate

The concrete eligible-shaped coefficient is b=(204/613)²; set
c=204/613, e=611/613, B=17b, s=Be, λ=c/r, and T=323λ².
The identities 17b=17c², 1−b/17=e² give the exact β=17, θ=1
branch of `OriginalPreparedTwists318.Eligible`. The reduced
denominator is 613²; b is a rational square, hence a square at
2,3,17, and its exact valuations are 4,2,2. It lies in (0,17).

Use P for both marked inputs: n=323 and nθ=323 are literally
identical. The final record's entries are

    parameter T = 80290702971648/203948703285721
    s = 432265392/230346397
    y₁ = y λ³ = 366402647525025600/125020555114146973
    y₂ = y(λs)³
       = 29594431554127905233054739927223785376972800
         /1528008230653594850778927294198023978386129.

All four entries T,s,y₁,y₂ are positive. The two original
(17b)-abscissas are B and B·s², on twists T and T·s²
respectively. This is the `TwoTwistPointRealization318.equalTwist`
formula with the same data; the 2/0 source target instead proves
the two actual field equalities directly and calls the untouched
`NormalizedPolePoints318.PointPair.certificate` with b≠0.
There is no separate global assumption for the second point in
this example. The certificate also retains its exact original
formulas e_source=T/b, s_source=s/b, p=y₁/(17b), q=17y₂/(B³s).

In the V13 original-seven-simultaneous-realization progression
the size-one beta support {17} and empty theta support have the
specific permissible fresh q₀=19 at threshold 0 and no excluded primes:
19≡7 mod12, (−1/19)=(3/19)=−1, (19/17)=+1.
Thus there is one **local selector-shaped** choice on the same pair,
both products 17·19. This does not assert that a proof-level
existential's chosen p is this tuple, or that no later threshold
or forbidden set disallows 19. It does not prove `RestrictedRC`.
The negative field/calibration auxiliary h*=−455 gives another
curve E_{323h*}=E_−146965, which is different from E_{nθ} and
is not needed for this rational point certificate.

## Exact disjointness from the four current prepared poles

For each detector slot 190,241,292, `DetectorPrimeProduct318.pole_product`
gives b_j=P_j z_j², with P_j the product of five distinct primes
and z_j≠0 by positivity. Thus no detector pole equals b, which
is square. In fact its Kummer beta support includes those five
selected primes >76176, so no such pole uses selected n=323 with
any coefficient.

For scalar slot 314, the same norm-coordinate margin and root
bounds feed `ScalarPoleRealDomain318.packed_bound`: (0<W<10).
Since R>10, A=114444R>1144440 and
b₃=A(W/(1+A))²<W²/A<1/10000, while b>1/10.
Thus this numeral does not match the scalar slot either.

There is a stronger arithmetic reason **no** current scalar
pole can give beta=17 or n=323; see `SCALAR-NONSQUARE.md`.
In particular none of the four coefficients of the original
same-key producer can use this two-twist example. The shared
integer, labels, h, contact parameter, three remaining point
pairs, and actual anchor are not supplied. A linked scalar
example must use different arithmetic support rather than
changing or reselecting a slot of the original row table.
