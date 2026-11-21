# A literal everywhere locally soluble relative tangent cover

This is a subsequent explicit isogeny-cover step over the actual
q=119851 negative split C, independent of the proof of abstract
Sel₄/₈ lifts. It constructs equations, but not a rational point.
The absolute degree is eight to J (one step after the degree-four
2-cover); it is not yet a multiplication-by-4 cover of J.
It remains a base-only calculation, never a statement about
the companion or any theta coefficient.

## Exact quadrics and map

Keep p=114649, q=119851, B=41579528353, b=4921145. On the literal C
the two conic projections in (x,y,u) and (x,y,v) have respectively
the seeds

    (1476564103,1510668638,90243)
    (3741536523,2063719442,743003829).

Each seed is checked on its exact conic. Parametrize by the
second intersection of a line with direction (m,n,0) through the
seed. For a seed (x0,y0,u0) on q x²−Q y²+F u²=0, the three
coordinates are

    R1=−q x0 m²+2Q y0 mn−Q x0 n²,
    R2= q y0 m²−2q x0 mn+Q y0 n²,
    R3= u0(q m²−Q n²).

Use Q=p for R and Q=9p for T. Each is a complete projective
parametrization over Q: u0 is nonzero, so every projective
line through the initial point has a unique direction with
third coordinate zero. The quadratic formula includes the
tangent direction and defines the isomorphism of the line
of directions to the smooth conic. The coefficient arrays
including R1,R2 and T1,T2 are exact in the JSON.

For \(\xi=1066808945=5\cdot1861\cdot114649\), take

    R1(m,n)=ξ T1(r,s),      R2(m,n)=ξ T2(r,s).

The map to C is \([R_1:R_2:R_3:\xi T_3]\).
Neither pair of parameters can be simultaneously zero since
neither R1,R2 nor T1,T2 have a common projective zero. The
geometric degree is two: given a point on both conics with the
same x:y ratio, the two conic parameter classes are determined,
and their common choice of projective scale leaves two
opposite ratios before taking the quadratic parametrizations.
There is an equivalent exact function field description:
if \(L_1,L_2\) are the tangent linear forms obtained by polarizing
the two seed quadrics and evaluating on C, the double cover
is \(\sqrt{(L_1/L_2)/\xi}\). To see the scaling, applying either
tangent to its own parametrization gives −2 times the square
of the polar pairing of the seed with the line direction.
So \(L_1/L_2\) reads precisely the relative conic parameter
scale modulo squares (inverse gives the same class). Apparent
zeros/poles of this function are interpreted via the normal
cover, not by treating a zero as a local squareclass witness.

## Exact support and why one local read per place is sufficient

The function divisor is \(2(D_1-D_2)\), where the \(D_i\) are
the degree-two pullbacks of the two conic seed points.
Their difference in the elliptic Jacobian J is the nonzero
2-torsion point \(T_0=(0,0)\): the two degree-two maps to the
conics have involutions negating v and u separately; on a
genus-one curve the product of these involutions is translation
by the difference of the degree-two divisor classes. Here
the product flips u,v and fixes x,y. In the actual standard
2-cover coordinates for root order (0,d,9d), the fixed first
root coordinate is the Weil character of \(T_0\), so the
nonidentity deck element in its kernel is exactly \(T_0\).
Thus the normal double cover is connected and étale, and its
Jacobian is the dual of the quotient by this \(T_0\).
The morphism of Jacobians is the genuine isogeny
\(\phi:E_d\to J\) with the original kernel \((d,0)\).

For any completion \(K\), choose a point \(P_0\in C(K)\)
away from the finitely many tangent zeros and poles. The
local squareclasses read by \(L_1/L_2\) are exactly the
coset given by its value at \(P_0\) times the image
of the marked quotient \(J(K)/\phi E_d(K)\) in
\(K^\times/K^{\times2}\). Indeed twist by the value at
\(P_0\); there is then a lift of \(P_0\), and identifying
origins on the two genus-one curves identifies the map with
that actual isogeny. The isogeny Kummer map in the root 0
coordinate is X, also the first coordinate of the full
Kummer map; see [Fisher §5](https://www.dpmms.cam.ac.uk/~taf1000/papers/higherdesc.pdf).
Thus the checked spanning local witnesses for J give the
whole direction space, not an upper guess from one sample.
For both signs of \(U,V\) it is the same affine coset, since
translation accounts for all C(K). At the real place shifted
J points have X class positive. On C take x=0,y=1 and the
negative square roots u,v; both tangent values are then
negative, so the chosen global class must be positive.

The only possible primes of a global \(\xi\) are those dividing
the two resultants:
\[
 \operatorname{Res}(R_1,R_2)=4qp B^2u_0^4,\qquad
 \operatorname{Res}(T_1,T_2)=4q(9p)b^2v_0^4.
\]
At other primes take primitive local representatives of the
two conic parameters; each ordered coordinate pair has a
unit entry, so the ratio of proportional pairs is a unit
after absorbing square changes of representatives. Those
primes are good for J and its first Kummer coordinate gives
both unit classes, so **every** unit passes there. The finite
support is therefore the old J primes plus 37,271,82555981
(from the chosen seed denominators), not a new conductor.
The squareclass necessity at these extra primes is not
dismissed just because the Jacobian has good reduction.

The checker computes literal rational x,y at each retained
place, exact square tests for the two ratios defining u²,v²,
and lifts the roots to sufficient precision to read the
squareclass of each tangent value. At odd primes use a
simple unit Hensel root (after removing the even valuation).
At 2 the chosen residue root is tested one additional digit:
a root mod \(2^{k+1}\) with unit (hence v₂ of derivative=1)
can be lifted in its residue class modulo \(2^k\); the code
keeps enough remaining bits to read the odd unit mod8.
All readouts are pinned in the output. These exact cosets,
plus the positive real sign, leave four positive squareclasses;
the smallest is the displayed \(\xi\). Each yields actual
local points of its associated relative cover at every place.
This is an explicit soluble Selmer representative, not merely
the assertion of existence by a global pairing.

The primitive raw model still needs minimization/reduction
to turn it into a useful point-search model. It is isogenous
to E_d at the Jacobian, so it does not lower the conductor
of the underlying elliptic curve. It may lower the search
height **after** model changes. At present no such point and
no arbitrary [4] coordinate equations have been found.

    python3 -B check_relative_tangent_lift.py | cmp - EXACT-RELATIVE-TANGENT-LIFT.json
