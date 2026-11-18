# A global first point and one coherent full Selmer lift on the actual partner

**For every individual prescribed prepared pole b, not a nearby b**:
one can write down a rational parameter E giving the actual first point
at x=B=17b with nonzero ordinate, such that the *fixed* partner curve
at parameter EV (V=B²(1−b/17)) has the specific full 2-Selmer class
(β,1,β). This class marks exactly the abscissa squareclass of B. There
are infinitely many such E, with distinct first and distinct second
twist squareclasses. They can be chosen so this partner Selmer class
does not come from rational torsion. Each partner then has either a
non-torsion rational point in the required full marked class or a
specific nonzero class in Sha[2]. The former gives an actual rational
PointPair at the *same* b; the latter is an obstruction to this marked
producer, not a disproof of every PointPair. No assertion of global
second point, a trivial Sha, full rank or original Values is made.

This construction includes all the actual indexed scalar poles and three
detector poles whenever their preparations are given. The same E is
used over Q and all completions for a *single* b; the four blocks need
not use a common parameter with each other. In particular this is more
than finding local e_p or only matching finitely many completions.
It does not select the four original poles or turn a substitute pole
into a prescribed one.

## Setup and explicit formula

Sufficient hypotheses are 0<b<17, b has square reduced denominator,
v2(b)≥3, v3(b)≥1, v17(b) even and ≥2. Set D=1−b/17, B=17b, V=B²D.
Write B=βu² and D=θz² with β,θ positive squarefree integers and u,z≠0
rational. In particular 17|β and β is not a square. Throughout the
three squareclass entries for E_n:y²=x(x−n)(x+3n) are in the order
x,x−n,x+3n with the usual root-derivative conventions at the three
rational points of order two.

Take ANY nonzero integer t divisible by 6βθ and define

    s=2t/(1−3βt²),  L=(1+3βt²)/(1−3βt²),
    e=(1−βt²)(1−9βt²)/(1+3βt²)²=(1−βs²)/(1+3βs²),
    E=B e,  P1=(B,4β²u³ s/L²).

The displayed denominators and numerators are nonzero; 1+3βs²=L².
Directly

    B−E=(2βu s/L)²,   B+3E=β(2u/L)².

Thus P1 is a rational point of E_E with nonzero ordinate and full
Kummer class (β,1,β). It is not torsion: the only possible nonzero-
ordinate rational torsion abscissa classes in this family are 3 and
−1 (see forward-prepared-nonzero-rank-transfer-r1), whereas v17(B)
is odd. The rational conic parametrization f(t)=e is already present in
the earlier two-seed paper; the new step is its *one-parameter local
image control at every prime of the actual fixed partner*.

## The same triple in the full 2-Selmer group of the fixed partner

Put n'=EV (squareclass βeθ). For the split full 2-descent of E_n'
we verify that the global triple δ=(β,1,β) is in every local Kummer
image. Its product is a square. At a rational torsion point (n',0)
the triple is (n',[4n'²],4n')=(n',1,n') in squareclasses; at O it
is (1,1,1).

* At 2,3,17, D is a local square: b/17 has valuation ≥3 at 2, ≥1 at
  3, and ≥1 at 17. At any other p|β the valuation of B is odd, and
  that of b equals it and is **positive**, since b has square reduced
  denominator. Hence D≡1 mod p is again a square there. At all these p,
  e is a local square as well: t is divisible by p (including 17 since
  17|β), and e≡1 mod p (indeed mod 8 at 2, using e=1−4βs²/L²).
  Consequently [n']=[β] and δ is the local image of (n',0).
* If p|θ outside these places, v_p(D) is odd. It cannot be negative:
  then v_p(b)=v_p(D)<0 would be odd, impossible by the denominator.
  Thus b/17=1−D≡1 mod p and B=289(1−D) is a local square; so β is
  a local square, and δ is the image of O. The real place also has
  trivial δ since β>0.
* At a new p∤6βθ where v_p(e) is odd, the denominator of e as a
  rational expression in t is a square and t is integral. An odd
  valuation forces p to divide at least one of 1−βt² and 1−9βt².
  In both cases β is a nonzero square modulo p, hence square in Qp:
  the same O handles **all** such additional primes, no matter how
  many prime factors the chosen integer introduces.
* All other p≥5 have v_p(n') even and all three entries units in
  squareclasses. Scale n' by a local square to a unit parameter;
  this preserves the marked classes and gives good reduction (the
  differences 1,3,4 times the parameter are units). For clarity,
  every triple of unit squareclasses with square product is in the
  local full Kummer image. Indeed over Fp the four rational 2-torsion
  points give #E(Fp)/2E(Fp)=4. The split Kummer map injects this
  quotient into the four triples with square product, so is onto.
  Lift a representing point by good reduction. If its reduction is
  neither O nor a root, all coordinates retain their unit squareclasses;
  if it is O or a root use the actual Qp torsion lift and the derivative
  convention. This proves the claimed full local image and avoids assuming
  global rank or a local-to-global existence principle.

These cases prove δ∈Sel₂(E_n'/Q). The associated full cover with affine
chart

    x=β r₁²,   x−n'=r₂²,   x+3n'=β r₃²

is everywhere locally soluble (avoid its finite boundary using any
smooth local point's neighborhood). Thus at every place the *same E*
achieves the requested two points, the first one already over Q.
This uses the full Kummer marking, not merely the corresponding
2-isogeny Selmer group. The first prime-depth filter papers did not
state that the first exhibited global point supplies this particular
global partner parameter.

## Force distinct twists, remove torsion and isolate the global obstruction

Exclude the finite support of 6βθ, of previous E values and of any
additional fixed primes. There is an odd prime q outside this set at
which β is a square: choose K divisible by the primes in the set and
take a prime divisor of βK²−1>1. Choose t a multiple of 6βθ and with
v_q(1−βt²)=1 by choosing a non-Hensel lift of the simple root modulo
q² and applying CRT. Then v_q(1−9βt²)=v_q(1+3βt²)=0 and v_q(e)=1.
Iterating and also excluding supports of B,V gives infinitely many
pairwise distinct classes [E], and hence distinct classes [EV]. If
[D]≠1 the two twists in a particular pair are nonisogenous over Q
by the non-CM j=35152/9 argument; distinct first twists across the
sequence likewise are pairwise Q-nonisogenous.

At this marker v_q(n') is odd and v_q(β)=0. The Kummer first coordinate
of (n',0) or (−3n',0) has odd q-valuation; that of O is 1 and of (0,0)
is −3 in squareclasses. None is [β]. All other rational torsion,
if present, has x-class 3 or −1, excluded by 17. In particular δ is
nonzero in Sel₂ modulo rational torsion images. The standard exact
sequence E_n'(Q)/2E_n'(Q) → Sel₂(E_n') → Sha(E_n')[2] → 0 now gives
a precise dichotomy for this *individual* marked cover. If δ lifts
globally, its representative has x=βr₁²≠0, with nonzero ordinate.
Set S=r₁/u; then x=B S², so the second point lies on exactly E_{EV}
at exactly the abscissa required by NormalizedPolePoints318.PointPair.
The two nonzero ordinates give non-torsion points. If δ does not lift,
its image in Sha[2] is nonzero; this does not rule out another marking,
another parameter, or a pair obtained by a different method. There is
no assumption of finiteness of the entire Sha.

## Reproducibility and scope

Run python3 verify.py and compare to REPLAY.json. Two finite controls use
previously specified exact b; they check the common formula, actual cubic,
three squareclasses and fresh markers. They do not constitute an explicit
global lift of the partner class. The theorem itself is uniform in the
prescribed b and can be evaluated using its squarefree class inputs.
The actual PointPair equations are NormalizedPolePoints318.lean in
quartics/quartic-318-326/proof/experiments/forward-two-twist-realization-r2,
commit a0950ac7c24df6d336a196966fb790d6abd55e44 (SHA256
410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542).
For the classical split Kummer map and Selmer exact sequence compare
[Silverman, The Arithmetic of Elliptic Curves](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf),
Chapter X. This is a mathematical proof plus finite checks, not a Lean run.
