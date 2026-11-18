# A density-one obstruction on the actual indexed scalar pole

For a natural-density-one set of integers a, there exists a rational prime
p(a), depending on **a only**, such that the complement D=1−b/17 of
b=PreparedIntegerSource318.scalarB(a,labels,h) is nonsquare in Q_p for
**every** indexed common elliptic chart h and every legal choice of labels
(and in fact independent of the last rational scalar correction Q). Thus
no equal-twist/square-complement realization can supply this indexed pole
for those a. The concrete progressions a=0,3,25,28 modulo 29 work with
p=29. This includes a=0,−1 at which the free 24-row scalar subsystem
admits a real-dense set of *square*-complement solvers. It pinpoints an
actual prefix identity that prevents those solvers from being glued.

Any PointPair at these actual poles would require **two Q-nonisogenous
quadratic twists** of the same elliptic curve. If both ordinates are
nonzero, they give positive rank on both nonisogenous twists, without any
independence claim for points defined on different curves. The argument
does **not** rule out a PointPair, assert a global pair, or prove or
disprove the whole construction.

## The source, not independently selected norm coordinates

Write t=a(a+1), r=4376874610839020+101783690143177584t+
800910366213064752t²+2642145132961084032t³+3147690941013049344t⁴.
Let L=114444=11·102², A=Lr, f(a)=1+A. For integer a, r>10, f>0;
r≡5 mod17 identically. In K=Q(√2), δ=(3−√2)²=11−6√2,
U=CoherentMultipleCharts318.chartU(h), T0=chartV(h). These are elements
of the fixed coefficient field and satisfy T0²=1−δU⁴ for all h.
The *actual* detector slots are J=Re(U²), H=Norm(U);
this is ScalarActualInputs318.detector33 and detector37.
Consequently the reused scalar N in ScalarForwardWitness318 equals

    N=1+(H/r)²+2J/r=Norm(1+U²/r).

Let Q denote the source's last rational coefficient, fixed by the actual
second labelled root and H. Its precise value plays no role below.
W=N²+rQ², b=A(W/f(a))², B=17b, D=1−b/17, V=B²D. Since J≥0, N≥1
and b>0. In particular B is nonzero and v17(B)=3+2v17(W/f(a)) is odd,
without requiring preparation.

## A finite-prime certificate independent of every chart index

Put T=(L²−11)²−72=171542649684398265553. Suppose an odd prime p∤L
divides f(a) and the four Legendre symbols of 2,11,17,T at p are
all −1. Then r≡−1/L, A≡−1 modulo p, and χ_p(−r)=χ_p(L)=−1.

1. Inertness of 2 gives the unramified quadratic field K_p with
   residue field F_(p²). Its normalized valuation has v_K(p)=1.
   If U is nonintegral, v_K(1+U²/r)=2v_K(U)<0. If U is integral
   and 1+U²/r vanishes modulo p, then U²≡−r. The quartic equation
   makes T0 integral and T0²≡1−δr². But the finite-field norm of
   1−δr² equals (1−11r²)²−72r⁴≡T/L⁴ modulo p, a nonsquare;
   a square in F_(p²) has square norm. Impossible. Thus
   v_p(N)=2v_K(1+U²/r)≤0.
2. χ_p(−r)=−1 makes x²+r y² anisotropic in the residue field.
   Dividing by the smaller valuation before reducing gives
   v_p(W)=2 min(v_p(N),v_p(Q))≤0 (allow v_p(0)=+∞). Hence v_p(b)
   is negative and even since v_p(A)=0 and v_p(f)>0.
3. We can write D as (W/f)² times ((f/W)²−A/17). The last factor
   is an integral unit reducing to 1/17, a nonsquare at p. Therefore
   the **exact local squareclass** is [D]=[17] in Q_p×/Q_p×².
   It equals [V] as well. This applies on the whole actual chart and
   does not rely on a heuristic distribution of scalar slots or indices.

At p=29 the four symbols are −1, r≡26 at every root of f, the norm
of 1−δr² is 2 mod29, and f has precisely the four roots above. At
a=0 specifically, v29(f)=1, so v29(b)≡2 mod4. As an extra direct
check, the literal parameter Hindex=1, n=−1 gives (J,H)=(456/1681,−8/41),
inverseNorm(−1)=1405152/4905889. The full exact b,D in REPLAY.json
satisfy v29(D)=−2, with nonsquare unit. These small indices illustrate
the scalar formula, not a claimed choice of the construction's four
required labels or prescribed CRT progression.

## Why this applies to almost every integer input

Let M be the splitting field of the *degree-eight* polynomial f over Q,
composited with Q(√2,√11,√17,√T). At 29 all the quadratic extensions
are unramified and the leading coefficient and discriminant of f are
units. Indeed f factors modulo 29 as

    11·X·(X+1)·(X+4)·(X−3)·(X⁴+2X³+10X²+9X−13),

with the quartic irreducible, checked exhaustively against linear and
monic quadratic divisors by verify.py. Thus the splitting field of f
is unramified there as well (all its roots lift in an unramified
extension by Hensel). Let C be the Frobenius conjugacy class of 29
in Gal(M/Q). Every prime in this class, outside finitely many primes
of bad polynomial reduction or dividing 2L·17T, has the same action
on the four quadratic subfields, and the same cycle type on the eight
distinct roots: four fixed roots and one 4-cycle. In particular f has
four distinct roots modulo each of these primes.

By the [Chebotarev density theorem](https://www.jmilne.org/math/CourseNotes/ANT210.pdf)
this class has positive prime density (positive Dirichlet density already
suffices for divergence of the reciprocal prime sum). For any finite
list of those primes the proportion of integers missing every bad residue
is exactly the CRT density ∏(1−4/p). These products tend to zero. The
exceptional a without any such prime divisor therefore have upper natural
density zero (on the positive integers or in symmetric intervals).
No uniform distribution of elliptic orders or unproved prime-values
conjecture enters the argument. More sharply, fix k: one may partition
the good prime set into k groups each having divergent reciprocal sum.
With density one an integer a hits at least one good prime in every
group, hence at least k distinct local obstructions simultaneously.
The quantifier here is each fixed k, not infinitely many divisors of a
fixed nonzero f(a).

## What it forces on a possible point-pair

Write E_t:y²=x(x−t)(x+3t); the two twists in a PointPair have t=e and
t=eV for a common rational parameter e (the PointPair.parameter,
not the rescaled Certificate.e). We cannot have e=0 since then y1²=B³
has odd 17-adic valuation. Also V≠0 by the local calculation. The
curves are quadratic twists of each other by the nonsquare V.
The short model is y²=X³−13t²X/3+70t³/27 and j=35152/9.
This rational noninteger excludes complex multiplication, since
[CM j-invariants are algebraic integers](https://arxiv.org/abs/2301.11169);
hence End over Qbar equals Z. A rational isogeny between these two
twists would, after composing with the standard isomorphism over
Q(√V), give a nonzero geometric endomorphism negated by conjugation.
All integral multiplications are fixed, a contradiction. Thus the curves
are not even Q-isogenous. If a rational solution has nonzero ordinates,
their x-squareclass is [B] in both curves; the odd 17-valuation excludes
the possible nonzero-ordinate rational torsion classes 3 and −1 by the
separate prepared-nonzero-rank-transfer packet (this application needs
only the odd valuation, proven above).

The square-complement specializations in forward-scalar-subsystem-sections-r1
are compatible with this theorem *because* they use two independent
common slots. The local obstruction is to the equality of twist classes,
not to local solubility of the unrestricted pair. The density-one quantifier
is on integer a, not primes' order compatibilities, full Values or density
of h. No assertion of Lean elaboration.

## Source and replay

Run python3 verify.py and compare with REPLAY.json. Source commit
a0950ac7c24df6d336a196966fb790d6abd55e44. Under
quartics/quartic-318-326/proof/experiments/forward-two-twist-realization-r2/
the exact identities are in CoherentMultipleCharts318.lean (sha256
01443a070ea295862a1c06111e8803651d6766afead3c3918797aa5718ba9bc9),
ScalarActualInputs318.lean (669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1),
ScalarForwardWitness318.lean (115729a9f8748290186bb0396ed78dd0355ec3fd93ff8a7ffb02f653dad675a5),
and PreparedIntegerSource318.lean (e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423).
For the optional explicit scalar evaluation use ActualScalarRoot318.lean and
CompressedAnchorWitness318.lean with the oriented constants (k,m)=
(−1+7√2/4,39/8−9√2/2) and generator R=(1+√2,2√2).
