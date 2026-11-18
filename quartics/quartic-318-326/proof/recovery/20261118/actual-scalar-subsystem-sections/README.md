# A literal scalar-subsystem construction and its generic section obstruction

**Object.** In stage0 take the actual scalar integer slot a, a fixed legal
integer root label n≠0,1 and its actual fixedRoot(n), but leave the two
common slots (w33,w37) independent of the *rest* of the 263-row prefix.
These are not model replacement polynomials. They are not yet the common
chartU(H) slots at a single selected integer H, either.

* For a=0 and a=−1 and **each** such n, there are rational assignments
  satisfying the actual scalar construction **and** its two-twist equations
  jointly (r263 through r286, 24 rows), with both ordinates nonzero,
  exact scalar preparation, square complement, and common slots
  arbitrarily close to **any** real point of the guard box
  0≤w33≤1, 1/100≤|w37|≤1. One may in particular take an interior open
  neighborhood lying entirely inside the strict guards.
* At **every** fixed integer a and legal n, on the generic field of those
  same two independent slots there is no rational-function PointPair with
  either zero ordinate, or with either free twist in a constant rational
  squareclass. In particular the specialization theorem is not a generic
  constant-class section. Nonconstant two-twist generic sections remain open.

## Literal source map

In forward-two-twist-realization-r2 (source hashes below), put
r=inputR(a), A=114444r, k=A/(17(1+A)²), c=inverseNorm(n). For a legal n,
0<|c|<1 by ActualScalarRoot318. With H=w37, J=w33 the exact source map is

    N=1+(H/r)²+2J/r,   Q=c/(H r^15),   W=N²+rQ²,
    b=A(W/(1+A))²,     B=17b,   D=1−b/17=1−kW²,   V=B²D.

Conversely H=c/(Q r^15), J=(r/2)(N−1−(H/r)²). This identifies the two
rational-function fields; at rational inputs only Q≠0 is required.
ScalarForwardWitness318.fill uses w0=a, w118=a², (w82,w83) the coordinates
of fixedRoot(n), and H≠0; r>10 gives its remaining denominators. The source
scalar_rows proves all 19 rows r263..r281 for any circuit coefficient S0.
NormalizedPolePoints318.PointPair is the system, with E the common free
parameter and s≠0,

    y1²=B(B−E)(B+3E),    y2²=B s²(B s²−EV)(B s²+3EV).

The certificate substitution e=E/b, s0=s/b, p=y1/B, q=17y2/(B³s)
gives 17p²=b(17−e)(17+3e), 17q²=b(s0²−e(17−b))(s0²+3e(17−b)).
Insert e,s0,p,q in slots 51..54 and e b,s0²,−(s0²−e(17−b))·
(s0²+3e(17−b))/3 in 315..317 as in ScalarCompleteSource318.finish.
These slots preserve the previous 19 rows and give r282..286.
No ternary anchor or r287, nor any of r0..262, is claimed.

## Obstruction on the generic two-slot function field

For all integer a, r≡5 (mod17): write inputR in the integer polynomial
in t=a+a²; the four nonconstant coefficients are divisible by 17.
Since A=102²·11r, v17(17A)=3. Let β be the positive squarefree
representative of 17A and write B=βu² with u a nonzero rational multiple
of W. Put F=Q(N,Q), L=F(√D). This is a geometrically integral quadratic
extension of F; over Qbar, choose v=N+√(−r)Q. W/v=N−√(−r)Q, so
Fbar=Qbar(v,W); D=1−kW² has two simple roots. The conic z²=1−kW² is
rational (point (W,z)=(0,1)), hence Lbar=Qbar(v,t) is purely
transcendental. In particular rational constants are relatively
algebraically closed in L.

Every L-point on any constant smooth projective genus-one curve over Q
is in fact constant over Q: extend to Qbar and apply properness and
Riemann–Hurwitz to rational maps from P¹, successively in v and t
(one may first extend the remaining function field to its algebraic
closure); then descend constants by regularity. If y1=0, E/B=1 or −1/3.
Set Z=(B/s)√D and Y=y2/(βu³s³). According to the anchor these satisfy

    Y²=β(1−Z²)(1+3Z²)   or   Y²=β(1+Z²/3)(1−Z²).

Both quartics are squarefree and give constant genus-one curves. Their
affine L-points must be constant, impossible since the involution negates
Z≠0. If y2=0 swap the two points by
(E',s',y1',y2')=(EV/s²,V/s,y2/s³,y1(V/s)³) and apply the same proof.

Further, E cannot vanish (B³ is nonsquare). If E is in n0 F×² with
n0∈Q×, then EV is in n0 D F×². Over L, after rational square scaling
the second curve is the quadratic twist of the constant curve
E_n0:y²=x(x−n0)(x+3n0). Untwisting sends its F-rational point to an
anti-invariant point of E_n0(L)=E_n0(Q), so it is 2-torsion, forcing
y2=0 (the given point is affine). If EV has constant class the same
argument interchanges the curves. No case with both classes varying
is ruled out. No specialization obstruction follows.

## An explicit fiber and simultaneous real/local density

For a=0,−1, r=4376874610839020, m=11r/4=12036405179807305,
A=204²m, β=17m=204618888056724185. On the rational conic set

    U=1+36β j²,  W=(1+A)j/U,  h=12j/U,  z=(1−36β j²)/U.
    b=m(17h)²=A(W/(1+A))²,  D=z²,  B=β(17h)².

For j≠0 everything here is nonzero (β nonsquare). Put v=17h,
e0=(1−β)/(1+3β), P=4β/(1+3β), so P²=β(1−e0)(1+3e0). Then

    E=B e0,  s=B z,  y1=β v³P,  y2=y1 s³.

Since V=s² these solve both original equations with nonzero ordinates.
Both are infinite-order points by the prepared-nonzero-rank-transfer
argument: the abscissa class β has odd 17-valuation. In this construction
the two twists are isomorphic by the displayed scaling; this is not a
construction of independent points.

The nontrivial norm condition is W=N²+rQ². The rational triple in SEED.json
solves it at j0=1927670569201332177589/29625763587158637529; verify.py
checks it by exact arithmetic, not a local norm test or a search assumption.
Here j0 and W0 both reduce to 1 at each prime dividing A. This seed alone
is **not** asserted to have common-slot real guards. The next step produces
simultaneous guards and finite conditions.

Require W(j)=W0 λ². For K=(1+A)/W0 this is the elliptic curve

    Y²=Kj(1+36β j²),  Y=λ(1+36βj²).
    X=36βKj,  Y'=36βK Y,  Y'²=X³+C X,  C=36βK²>0.

The point P0 at (j0,λ=1) has infinite order. At 7 and 19, C reduces to 4
and 17 respectively; these are good primes and the group sizes are 8
and 20 by direct count (also by χ(−1)=−1). Prime-to-p torsion injects
under good reduction: use 7 for odd primes other than 7, and 19 for 7.
The sole nonidentity rational 2-torsion class is (0,0), since C>0.
Its rational half would have X²=C by the duplication formula
X(2P)=(X²−C)²/(4Y'²), impossible as β is nonsquare. Hence only the
origin and (0,0) are torsion; P0 is neither.

The real elliptic group is a circle (the cubic has one real root), so
multiples of any nonzero multiple of P0 are dense there. At the finite
set p|A, any prescribed small neighborhood of P0 contains a coset
P0+U_p of an open subgroup of the compact p-adic elliptic group; the
subgroup has finite index. Choose M divisible by these indices. The
points (1+Mk)P0 therefore retain j≡1 (mod p) and W≡1 (mod p) at all p|A,
and are still real dense. Consequently positive W's achieved, with
W/W0 a rational square, are dense in (0,(1+A)/(12√β)), the full open
range of W(j) for positive j. Exclude the point at infinity and the
finitely many zeros.

For each such W, scale the recorded norm pair by λ to obtain a rational
point on N²+rQ²=W. Rotate it by the rational norm-one circle, whose
parametrization is ((1−r t²)/(1+r t²),2t/(1+r t²)); these rotations
are dense on each real ellipse. Thus the available (N,Q) are dense
throughout the open annulus 0<N²+rQ²<(1+A)/(12√β). To see the
simultaneity explicitly, choose a nearby attainable W, scale the target
direction to that ellipse over R, and approximate the direction there.
Return via the inverse formulas, continuous for Q≠0. Any guarded target
has 0<W≤(1+1/r²+2/r)²+10000/r^29<2<(1+A)/(12√β), uniformly
over all allowed n since 0<|c|<1. Thus genuine rational *free* slots
with the claimed accuracy exist for every such n. No approximation of
the actual elliptic abscissa relation is upgraded to equality here.

The scalar pole has precisely the prescribed arithmetic: since W is a
unit at every p|A, v_p(b)=v_p(A) there; elsewhere v_p(b) is even.
Its reduced denominator is therefore a square, and v2,v3,v17=(4,2,2).
The class m is 1 modulo 8,3,17, hence square locally at all three.
0<b<17 follows from the nonzero j,z and conic equation. As real
targets vary, b is nonconstant locally in J whenever N≠0 (as here);
these are infinitely many distinct poles, not just assignments with
the same value.

## Scope and reproduction

PreparedIntegerSource318.scalarB substitutes the previous 263-row witness:
J=((chartU(Hindex))²).re and H=normCoefficient(chartU(Hindex)) at the
**same** indexed multiple. A dense set of free rational slots satisfying
the box and any open neighborhood of these coordinates does not fix those
two identities, does not realize a prescribed indexed pole, and does not
settle Values, the three other pole blocks, the anchor or the final
polynomial. The nonsquare generic obstruction also does not rule out
individual indexed poles. This is a paper/source and rational-replay
packet, not a new Lean elaboration.

Run python3 verify.py and compare output to REPLAY.json. Source basis:
commit a0950ac7c24df6d336a196966fb790d6abd55e44, directory
quartics/quartic-318-326/proof/experiments/forward-two-twist-realization-r2.
SHA-256 of the six source files:

    115729a9f8748290186bb0396ed78dd0355ec3fd93ff8a7ffb02f653dad675a5 ScalarForwardWitness318.lean
    97d42237dd200a73ebcac4a0d9cf88c7a83fba4fa6abe5e8d5b52f92f00edcc2 ActualScalarRoot318.lean
    410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542 NormalizedPolePoints318.lean
    a0f74e00bdd0be89dee1cac08d935908bb225610dba88d9564d9c99916a03323 ScalarCompleteSource318.lean
    669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1 ScalarActualInputs318.lean
    e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423 PreparedIntegerSource318.lean
