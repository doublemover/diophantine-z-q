# Two actual completed-support candidates share an everywhere locally soluble genus-one cover

**Scope.** Fix the exact original scalar J, labels, three scales and
sixteen admitted residue contacts (1e1266ba). This is a paper existence
result for two order-compatible positive squarefree classes and their
single two-equation compatibility cover. There is a common real-accepted
h and local points in the prescribed residue balls at every place.
No rational point on the cover, weak approximation for its rational
points, numerical new primes, full pole denominators, or PointPair
is asserted.

Take the two literal singleton classes

    a: slot 241, theta_a=−32/407, p_a=415721;
    b: slot 292, theta_b=  1/2399, p_b=9807649.

Let the fixed rational scaled roots be s_a=theta_a/c_1²<0 and
s_b=theta_b/c_2²>0. They are nonzero and distinct; all numerators
and denominators of s_a,s_b,s_a−s_b lie on the router support B.
The values c_1,c_2 are the same actual fixed scales, not adjustable
witnesses.

## 1. Reapply the order-compatible prime producer after updating the anchor

Use the already independently checked pilot-clone and gcd-sieve proof
336708e6 to obtain q_a and sigma_a=p_a q_a, with the actual first class
completed. Denote by h_a mod L_a the CRT with the old sixteen rows
and the q_a primary/opposite and depth-threshold clauses. In particular
L_a is a multiple of L and h_a≡h* mod L. Let S'=S∪{q_a}; at q_a
fix a residue w_(q_a) mod q_a² from the first conic construction.
It is a unit and the target a factor has depth one there. Keep every
old w_p mod p² for p in S. At every p in S' the a-conic has a
local solution with the corresponding exact ball; at exactly p_a,q_a
among these p the a-factor has depth one.

Use the exact b pilot at p_b, primary root rho=8296152 mod p_b.
Its two actual group sizes and point orders are

    primary     #E=9813764,  ord R=2453441;
    opposite    #E=9801536,  ord R'=29.

The direct finite point count in the companion replay gives gcd 4,
and the literal independently checked XVI rows give the point orders.
Also p_b≡1 mod8, (7/p_b)=−1, theta_b is square at p_b, and its
old target value has exactly p_b depth one. Crucially this pilot
still satisfies all order caps for h_a mod L_a: its point orders
divide h_a and h_a−1 respectively because the original XVI clauses
are still included. Additional anchor prime factors from q_a do
not invalidate this observation.

Apply the same proof of 336708e6 with pilot p_b, anchor h_a,L_a
and recorded set S' instead of p_a,h*,L,S. Here is the exact
compatibility check behind this use:

* q_a lies outside B and is 1 mod8, just like every member of S,
  and p_b is still the **only** p in S' hitting class b. The router
  establishes the latter at q_a because that p hits class a.
* Strip all prime powers in S' from L_a before forming the
  pilot-clone field. Thus it is still unramified above S' over
  Q(i), including the newly added q_a. Finite Kummer order caps
  at all other anchor primes are read from the same marked p_b
  Frobenius after cloning. The Gaussian ray field supported on S'
  is disjoint by the same abelian unramified-intersection and
  Gaussian class-number-one argument. No field containing q_a's
  torsion at q_a is required.
* At each p in S' prescribe the b-conic's exact residue bit
  (q_b/p), with the p_b factor stripped only at p_b. The two
  split coordinates can again avoid mu_4, so both new group counts
  are units at every p in S'. In particular q_b's orders introduce
  no conflict with the existing q_a-depth progression at q_a.
  All other shared order factors are controlled by the updated
  Kummer caps and the same odd-group-gcd sieve at q_b.

The proof supplies a distinct q_b outside B and S' with
q_b≡p_b modulo 8B and the indicated b phases, and a compatible
even CRT extending h_a mod L_a. Hence there is an actual common
h accepted by the real norm test, using the reviewed density proof
629a0483. Both q_a and q_b satisfy the original strong oriented
order and p³-depth clauses in this final progression.
Put sigma_b=p_b q_b. Each sigma is positive, squarefree, and a
local square at every prime dividing B. Their supports are disjoint.

## 2. The second unseen prime does not obstruct the first equation

Consider the same w for

    w²−s_a=sigma_a U²,       w²−s_b=sigma_b V².                (1)

Dividing the two literal factor equations by c_1² and c_2² only
changes ordinate normalizations, not squareclasses. At p in S'
both local square conditions hold for the entire retained ball
w_p+p² Z_p, by construction of sigma_a and the exact new b-phases.
In particular one can choose a solution to both with the exact
old w_p here, not just separate w-values for the two equations.

At the new unseen q_b, the b equation requires w²≡s_b. To verify
the a equation there, let p range over the two factors of sigma_a.
They belong to S' and have w_p²≡s_a mod p. The b-ray condition
at these p, where b is a unit and p_b≠p, is precisely

    (q_b/p) = ((s_a−s_b)/p) (p_b/p).

All four support primes are 1 mod4. Multiplying and using
quadratic reciprocity gives

    (sigma_a/q_b) = ((s_a−s_b)/sigma_a) (sigma_a/p_b)
                  = (sigma_a/p_b).

The middle Jacobi term is +: the rational difference is supported
on B, sigma_a is a local square at every prime of B, and
sigma_a≡1 mod8. At the old p_b ball, class a already has its
unit square, so

    (sigma_a/p_b)=((s_b−s_a)/p_b)=((s_b−s_a)/q_b).

The last equality uses q_b≡p_b mod 8B and reciprocity on the
same rational difference. Thus at q_b the a-unit quotient is
a square whenever w²≡s_b. Choose V=1 and lift
w²=s_b+sigma_b (theta_b, and therefore s_b, is a square unit
mod q_b); this gives exact b-contact depth one and the required
a-unit simultaneously. At q_a the b condition was directly
included in the new S' ray. This is the asymmetry of the
two-stage construction; no unidentified cross symbol is assumed.

## 3. Smooth model and local points at all remaining places

Let C be the projective intersection in coordinates [W:Z:U:V]
of the two quadrics

    W²−s_a Z²=sigma_a U²,
    W²−s_b Z²=sigma_b V².

It is smooth in characteristic zero, and has smooth reduction at
p outside B and the two supports. In such a characteristic (odd),
if a linear combination of the two rows of its Jacobian vanishes
with both coefficients nonzero then U=V=0, and the two equations
force W=Z=0 because s_a≠s_b. If exactly one coefficient is
nonzero then its equation forces its three coordinates W,Z and
U or V to vanish by nonzero coefficients, and the other equation
forces the fourth to vanish. Neither is a projective point.
The same proof works modulo each indicated p.
The two independent radicals of w²−s_a and w²−s_b give a connected
fourfold cover of the w-line: they each have two simple and disjoint
branch points, and no ramification at infinity. Riemann–Hurwitz has
total ramification contribution 8, so the geometric genus is one.

At every p|B, both sigma values are local squares; take the same
w sufficiently negative in valuation, so both factors are squares
by the router principal-unit argument and the chosen stronger
bounds are satisfied. Over R take w large and positive, so both
factors are positive. At p in S' and at q_b use the exact balls
proved above. At all remaining primes, the smooth geometrically
integral genus-one reduction has an F_p-point. For precision, this
does not presume an elliptic origin: over F_p choose a geometric
point P and let T=Frob(P)−P on its Jacobian. Frob−1 on this
elliptic Jacobian is a nonzero finite isogeny (its differential
is −1), so choose a geometric Q with (Frob−1)Q=−T. Then P+Q
is rational. After this point, the usual elliptic Hasse bound
[Sutherland Thm. 8.1](https://math.mit.edu/classes/18.783/2015/LectureNotes8.pdf)
shows there are more than 12 points, since p>76176. Only at
most four lie in each of Z=0, U=0, V=0 (use the two equations
in the corresponding plane). So choose an affine point with
nonzero ordinates and lift it by smooth Hensel. This supplies
local solutions everywhere and **not** a single rational w.

## 4. Exact actual Jacobian and the marked 2-torsor

Set D=sigma_a sigma_b and let

    E_D: y²=x(x−D s_a)(x−D s_b).
    x=D w²,              y=D² w U V.                       (2)

Equation (2) is the literal map from the affine chart of C to E_D;
multiplying the quadrics verifies its equation directly. It extends
to a morphism of smooth projective curves, has degree four (eight
generic signs with fixed w², U², V², of which four fix y), and its
deck group is exactly the four sign changes of (w,U,V) with even
sign parity. Over an algebraic closure choose as origin a preimage
of the identity of E_D. Then the map is an elliptic isogeny.
Each deck transformation is translation by its difference at
the origin: the pointwise difference has image zero on E_D
and is constant into the finite kernel. The deck group is
(Z/2)², so that kernel is the full geometric 2-torsion.
Equivalently the induced morphism Jac(C)→E_D factors through
[2] on Jac(C) and an isomorphism to E_D, and this factorization
descends to Q by uniqueness. Thus C is the exact [2]-cover of
this actual Jacobian. Its standard ordered squareclass label is

    (x, x−D s_a, x−D s_b) ↦ (D, sigma_b, sigma_a),

since the three literal square multiples in (2) are respectively
D w², sigma_b·(sigma_a U)², sigma_a·(sigma_b V)².
In particular compatibility is an actual torsor class
[C] in Sha(E_D)[2], not an assertion that it vanishes.
For instance, choose a geometric origin over O; its Galois
translations lie in the displayed kernel, so the torsor class
has order dividing two. Local points are the just-proved
Sha membership.

The original E_n proportional-root family cannot be substituted
for this Jacobian using a scaling/isomorphism. Here the negative
Legendre cross ratio s_a/s_b is

    −(32·2399/407) (c_2/c_1)²,

of squareclass −2·2399·407. The negative values in the sixfold
cross-ratio orbit of −3 for the original proportional roots
(0,n,−3n) are −3 and −1/3, both of a different squareclass.
Thus even the j-invariant need not be imported from that family:
for these two actual roots it is different.

There is also no split-binary shortcut on parametrizing the
first rational conic. The branch points of the second double
cover on that conic have w²=s_b and U²=(s_b−s_a)/sigma_a.
Their residue field is the full biquadratic field
Q(sqrt(s_b), sqrt((s_b−s_a)/sigma_a)). Indeed s_b is nonsquare
(squareclass 2399), and the second radicand has an odd valuation
at p_a outside B, where s_b is a unit. The two classes are
independent. All four branch points are therefore one rational
conjugacy orbit. In any rational parameter of the first conic
the squarefree branch quartic is irreducible, not a product of
rational linear or quadratic factors. This structural fact is
not a proof either for or against a rational point on C.

Even if [C]=0, one must still find a rational point in the
simultaneous open neighborhoods (or prove the needed approximation
property for this elliptic torsor), rather than appeal to conic
weak approximation. A positive rank or local solubility alone
does not give all these prescribed local components and balls.

## 5. Why transferring one completed factor per slot is not enough

Independently rational single-factor parameters cannot be assigned
to three original slots: the literal source uses one shared t.
In general r distinct nonzero scaled roots give a connected
2^r-fold cover of the same w-line, with 2r disjoint simple branch
points and ramification index 2 at each; its genus is
1+2^(r−1)(r−2). Thus even one chosen factor in each of three slots
requires a single genus-five shared curve, not three independent
conic rational points. The two-factor construction above is a
genuine common local compatibility milestone. It does not
assert a rational parameter on that genus-one cover, and does
not construct the genus-five rational parameter.

The finite companion replay checks the same second pilot's
two point counts and exact order/CRT records:
    python3 -B check_second_pilot.py | cmp - EXACT-SECOND-PILOT.json
    sha256sum -c SHA256SUMS
