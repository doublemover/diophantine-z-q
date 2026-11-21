# The actual early leaves force an oriented split contact

This is a further paper result on the three literal scaled detectors with
their one common h and actual labels. Take the same guarded witness, a
nonzero original pole b, and a literal PointPair for it. At a prime
p not in {2,3,7,17} where c and Delta=c²t−1 are units, suppose
e=v_p(F(c²t))>0 is odd.

Write K=Q(sqrt(2)), d_c=3−sqrt(2), D_c=d_c² and
R=(1+sqrt(2),2 sqrt(2)) on the actual curve y²=x³−D_c x. Then:

1. **p splits in K.** In one orientation (w,wbar), [2h]R reduces to O
   at w, and [h−1]R reduces to O or T0=(0,0) at wbar. The
   orientation is unique.
2. For p≠41 the positive arm w alone must supply norm depth at
   least 3e+1. If p does not divide h, the first return [a_w]R of
   the actual generator (a_w its exact residue order) already has
   formal parameter divisible by p^(3e+1), in particular p^4.

Thus inert primes and both-positive split arms cannot supply odd
contact, irrespective of making h extremely divisible. This is
necessary, not sufficient, and does not exclude every remaining prime.

## 1. Exact valuations before the last six folds

At every extension of v_p to K the three detector weights have values
−e,−7e,−25e. All sixteen exact unweighted coefficients have even
valuation or vanish, by ConstructedLeafParity318.all_even applied to
DetectorGateWitness318.witness_first107 at the same guarded witness.
The two required units are 2 and 11+6 sqrt(2), of which the latter has
norm 49. Hence in each step X_k=X_(k−1)²+leaf_k a finite square
valuation is even and a finite leaf valuation odd. If one leaf has
valuation <=−e, then that step has valuation <=−e, including when
the previous term vanishes. Subsequent steps have value at most double
the preceding value once it is negative. No integrality of the other
coefficients is needed.

The eight exact early leaves, indexed from 1 in ActualDetectorFold318,
are

| positions | unweighted coefficient for j=0,1,2,3 | weight |
| --- | --- | --- |
| 3,4,5,6 | U([n_j h]R)² | w151 |
| 7,8,9,10 | conjugate of V([n_j(h−1)]R)−1 | w151 |

The first row is PrefixDetectorLeaves318.leaf1_square through
leaf4_square together with SelectedActualChartLeaves318.actual_u.
The second is its linearLeaf, actual_v and conjugated_delta for
the second four charts. The conjugation is literal: the condition
on V−1 belongs to the *opposite* place when p splits. The scaled
view changes these weights, not their coefficients.

Call an arm early-good if all eight listed coefficients have positive
valuation (allow zero via infinity). If not, one coefficient at or
before position 10 has valuation <=0, and its weighted leaf has value
<=−e. At least six folds remain, so the final X at that place is
nonzero of valuation <=−2^6 e. If neither arm is early-good, the
rational inverse trace 1/X+1/conjugate(X) therefore has valuation
>=2^6 e or is zero. In the latter case literal total division gives
b=0, excluded. Otherwise v_p(b)<=e−2·2^6 e<0, with odd parity
because the trace quotient is squared. This violates the literal
PointPair denominator guard dd5d6ca1. Thus some arm must be early-good.
The argument is valid also when the conjugate valuation is the same
(inert case), and for any positive odd e, not only e=1.

## 2. Exact interpretation in the residue group

The coherent half-point charts have

    U(P)²=1/x([2]P),
    V(P)=(x^4−6D_c x²+D_c²)/(x²+D_c)²,
    V(P)²=1−D_c U(P)^4.

At O their values are U=0,V=1. At an odd good prime, exact criteria
are

    v(U(P))>0     iff Pbar is in E[2],
    v(V(P)−1)>0   iff Pbar is in {O,T0}.

For the first, at nontorsion P use x([2]P), of negative valuation
exactly when [2]P reduces to O; exact O and 2-torsion give U=0
directly. For the second, V−1 positive implies U positive by the
chart equation and D_c unit. At the four remaining residue points
V is regular, takes 1 at O and T0 (at O the highest powers of x
cancel), and is −1 at (+d_c,0) and (−d_c,0). These signs differ
in the residue field. None of their finite denominators vanish.

An early-good orientation therefore requires [n_j h]Rbar in E[2]
at w for all j and [n_j(h−1)]Rbar in {O,T0} at wbar for all j.
The original source Lucas equation,
n_2²−n_1(n_1−2)n_2 n_3+(n_1−2)²n_3²=1, forces gcd(n_2,n_3)=1.
Bézout then removes these multipliers in each residue subgroup:
the eight conditions are equivalent to [2h]Rbar=O at w and
[h−1]Rbar in {O,T0} at wbar. These are early unweighted conditions
only, not the stronger sixteen positive weighted valuations.

If p is inert both conditions hold in the same residue group and
imply [2]Rbar=O, impossible since y(R)=2 sqrt(2) is a unit. If p
splits, the opposite condition forces [2h]Rbar=[2]Rbar in that
opposite group. The latter point is not O; this also proves
uniqueness of the orientation. For p≠41 it is not T0 either:
the duplication numerator x(R)²+D_c=14−4 sqrt(2) has norm
164=4·41, and 4 y(R)² is a unit. Thus the signed depth theorem
8f4cc314 has exact type (+,0), no (+,+) or (+,−), and the
threshold 8a0f698e gives

    mu_w+v_p(h) >= 3e+1,    mu_w=v_w(z([a_w]R)),

since the split residue order is p-unital. At p=41 a T0 pole in
the opposite arm is not excluded by this calculation and cannot
be silently dropped.

At the specific full h from 5076da44 none of the 17 nonfixed
primes dividing h passes both orientation and depth: both-positive
arms cannot orient, all inert primes are excluded, zero-zero has
no positive arm, and the only split (+,0) candidate p=89 has
depth two. The fixed contact exceptions require their own checks.
Combining with the prior widened-support theorem makes the required
outside-h prime at least fourth-depth on one specified positive arm,
not just ordinary Wieferich in some arm. No such prime is supplied.

## 3. Exact finite test for varying h, retaining the original t

For a nominated fixed contact t and the actual label tuple, the
three original scales are independent of h. For each nominated
good odd contact prime p≠41, collect its largest positive odd e
over all incidences. Its orientation is common to these incidences.
Put a=order(Rbar) on the primary arm, b=order(Rbar modulo {O,T0})
on the opposite arm, and mu=depth of the first formal return on
the primary arm. Then the necessary orientation-and-depth tests
above are exactly

    h = 0 mod M_plus,  h = 1 mod M_minus,
    M_plus = lcm(a/gcd(a,2), p^max(0,3e+1−mu)),  M_minus=b.

Choosing a conservative lower bound mu>=1 can ensure the depth
by requiring more divisibility, but failure of that stronger
version does not reject the exact condition. These moduli are
not asserted equal to SelectedQuotientOrders318.order, whose
native module uses the full half-point formal subgroup, not this
weaker necessary quotient. That stronger original sufficient trace
construction also uses actual Padé precision for all sixteen leaves.

To retain a finite local center h=h0 mod L, generalized CRT says
exactly: every cross gcd of a zero modulus and a one modulus is
1; gcd(M_plus,L)|h0; gcd(M_minus,L)|(h0−1). Same-target
conditions are compatible automatically. A violation can forbid one
orientation or one pair of orientations, so this is an exact 2-SAT
test for **the necessary modular conditions**. With a component
return dividing h0 and L, the chosen CRT residue and its lcm
step both lie in that component; a nonempty retained open real
region is met on the positive tail by the same
MixedCRTComponentSelection318 argument. This can retain finite
old scalar local neighborhoods, not the exact old scalar b or
its latent prime support.

For example under the old retuned center (h0 divisible by 2,3,5,17,
and L a multiple of each), none of the old 313,577,1489 candidates
can be salvaged just by deepening h. At 313 the actual opposite
quotient orders are 3 and 17 (the full first-arm order is 6 and
its midpoint T0). At 577 they are 12 and 145; at 1489 they
are 356 and 778. Every possible opposite modulus conflicts with
the corresponding fixed old local residue. These are exact
finite orbit checks, not a Gaussian count assumption. This
criterion does not furnish a contact parameter t with compatible
full support, let alone the rational points on the resulting poles.

## Pinned source

SHA-256 prefixes of the original sources: ActualDetectorFold318
1bb3b85f, ConstructedLeafParity318 31eb4290, CoherentMultiplePrefix318
54c2bffb, CoherentMultipleCharts318 01443a07, SelectedActualChartLeaves318
eb035d67, PrefixDetectorLeaves318 c1009588, MixedCRTComponentSelection318
eb3813bf, SelectedQuotientOrders318 2c82f5dd. The paper proof uses
the actual unchanged folded coefficients and chart signs. No Lean
run, generic-rank claim, or unconditional witness.
