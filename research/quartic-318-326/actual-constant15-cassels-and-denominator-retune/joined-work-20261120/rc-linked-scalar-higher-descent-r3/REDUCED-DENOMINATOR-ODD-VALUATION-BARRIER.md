# Exact denominator-character reduction to exceptional crossed local poles

Same fixed scalar c=12W/(1+A), W=N²+R_input Q²,
N=Norm_K(1+U(h)²/R_input), Q=Norm_K(U(i))/(Norm_K(U(h))R_input^15),
i=s−1=m h. Here K=Q(√2) is the source chart field, DIFFERENT
from Q(√β) used in the residual genus-one covers. For these exact
indices v₂(h)=6, v₂(i)=22, v₂(m)=16.
Take η=−2·1861·2027·83761 from the conditional pairing.

The four fixed primes dividing 1+A are 29,181,1346909,70850399941.
Each is η-split by Euler's criterion, so its exact denominator
valuation is immaterial to the sign (η/Z). All primes dividing
2·3·β·R_input, including 1861, are nonnegative c-valuation by the
certified original scalar W units (at 2 and 3 use the actual positive
valuations of 12; 1+A is a unit). Prime 7 has c≡1 by the already
independently verified local source row. Thus to compute (η/Z) only
odd negative c-valuations outside this finite set matter.

At any remaining prime p, R_input and 1+A are units. A negative
odd valuation of W is possible only if v_p(N)=v_p(Q)<0 and their
leading squared summands cancel to odd extra depth. If the two
valuations were distinct, the minimum would be even. If both
were nonnegative there could not be a pole. This cancellation
also forces (−R_input/p)=+1.

At an inert source prime (2/p)=−1 no chart poles can occur for U(h)
or U(i). Here is an all-prime check, not an inference from a finite
scan. The good cubic E: y²=x³−(3−√2)²x is a quadratic twist of
E0:y²=x³−x over F_(p²). If p≡3 mod8, E0 has trace 0 over Fp
by pairing x and −x. Its two possible quadratic twists over F_(p²)
have cardinalities (p±1)² with v₂ at most 4.
If p≡5 mod8, write p=a²+b² with a odd, b≡2 mod4.
Over Fp the trace of E0 is ±2a. Indeed with quartic character ψ
and quadratic χ the trace formula is minus the sum of
J(ψ,χ) and its conjugate (substitute x² in the point count).
The Jacobi sum is a Gaussian integer of norm p, by the Gauss-sum
product formula; the real part is odd because E0 has full rational
2-torsion and p+1≡2 mod4. The trace over F_(p²) is then 4a²−2p.
The two cardinalities are (p+1)²−4a² and (p−1)²+4a².
For the first, factor as Norm(a−1+bi) Norm(a+1+bi):
one factor has 2-adic valuation two, the other three
(since b≡2 mod4). The second has valuation two since p−1 has
valuation two and a is odd. Thus both cardinalities have
v₂≤5. Multiplying any residue point by h or by i, divisible
by 64, gives odd order. A pole of U requires order four,
since the literal doubled abscissa is x([2j]R)=1/U(j)²
and affine x=0 is the nontrivial 2-torsion point.
Thus both U(h),U(i) are integral at the inert prime;
N is integral and equality v(N)=v(Q)<0 is impossible.

Now suppose p splits in K and W has odd negative valuation.
At one of the two completions the chart U(h) must have a pole
because v(N)<0. Write v_p U(h)=-a<0 there. This reduction
point has order four, so −1 is square in Fp: a pole can only
occur at an affine source denominator x²+(3−√2)²=0 with
its numerator unit at good odd p. The identity x([2h]R)=1/U(h)²
shows that the doubled point is near T=(0,0), with local
formal translation depth a (x vanishes to order two at T).
Since m is even, [2i]R=[m]([2h]R−T) is formal and its depth
is a+e, e=v_p(m), by the formal logarithm. Hence U(i)
has valuation a+e at that same completion. If U(h)
is itself a zero at the other completion, applying the same
doubled identity at O gives v(U(i))=v(U(h))+e there.
If U(h) has a pole at BOTH completions, U(i) is positive-depth
at BOTH. In either of these two configurations Q cannot
match a negative v(N). Consequently the other U(h) must be
a unit.

At the other completion write
ε=v(1+U(h)²/R_input)≥0. Then v(N)=−2a+ε<0.
Equality requires that U(i) have a pole precisely at this
OTHER completion, of order b determined by
    v(Q)=2a+e−b = −2a+ε,
    b=4a+e−ε ≥2a+e+1≥3.
Thus two genuine opposite-place poles, and the second one
with depth at least three, precede any relevant cancellation.

There is an extra purely finite-field splitting constraint.
At both completions E is a twist of y²=x³−x, by 3∓√2.
If (7/p)=−1 these twists have opposite traces. Since (2/p)=
(−1/p)=1, p≡1 mod8, so their two cardinalities sum to
2(p+1) of valuation two. They cannot BOTH be divisible
by 8. The required two chart poles would force that (in fact
very much more) because the elliptic indices h,i are divisible
by 64. Thus an unresolved denominator prime also satisfies
(7/p)=+1. At the completion where U(i) has its pole, the
point [i]R has residue order exactly four, so the order of
R itself is divisible by 2^(22+2). The Hasse bound yields
    p ≥ (sqrt(2^24)−1)² = 16,769,025.

In summary the exact denominator character reduces to the
product of (η/p) over odd-pole primes of W occurring only
at the crossed valuation configuration just proved, with
p≥16,769,025 and χ_p(2)=χ_p(−1)=χ_p(7)=χ_p(−R_input)=1.
Once v(N)=v(Q)=-d<0, the contribution requires the actual
unit sum p^(2d)W to have odd valuation LESS than 2d; the
class conditions alone do not decide that depth.

This is not a computation of the reduced denominator sign.
The auxiliary quadratic character η is not generated by
the four splitting characters (it has the distinct support
primes 2027,83761); their splitting alone does not force
η-splitting (e.g. 233 is a finite-character counterexample,
not an actual denominator prime and not within the pole bound).
An effective factor certificate or a global parity identity
for this crossed-pole cancellation remains necessary.

## Why residue propagation alone does not remove this gap

An unreduced positive rational representation c=n/d gives
Z=d/gcd(n,d). For odd primes away from the conductor of η,
the exact character is the quotient of the characters of d
and gcd(n,d), not determined by c modulo the conductor.
Arithmetic-circuit evaluation can track d modulo the fixed
conductor before reducing; doing so does not track this gcd.
For this particular source the only still-uncontrolled factors
in the correction are what produce the odd local W poles
described above.

Even knowing the representation W=N²+R_input Q² and any
finite set of its local residues does not determine the
reduced denominator sign *as a general principle*. To see
this, start with rational N,Q approximating those residues
to the specified finite precisions (including all four
primes dividing 1+A), with denominators supported on that
finite set. Pick an outside prime q that is split for −R_input
and nonsplit for η (233 illustrates that the additional
quadratic splits do not change this issue). Add q to the
allowed denominator of N,Q and use CRT on their integer
numerators, keeping the same local approximations on the
original set and arranging near q that
    N=a/q, Q=b/q, q∤ab, v_q(a²+R_input b²)=1.
For b a unit, choose a root modulo q of a²=−R_input b²,
then perturb modulo q² away from its single Hensel lift.
The new W has valuation −1 at q without changing the
retained local data. Other denominator valuations of
12W/(1+A) can be kept unchanged by taking those
approximations sufficiently close where needed. Its
reduced denominator character therefore flips. This is a
counterexample to the proposed norm-plus-CRT inference,
not a counterexample with the literal elliptic h,i or the
required high-order crossed poles. A proof for the actual
c still needs those elliptic cancellations.
