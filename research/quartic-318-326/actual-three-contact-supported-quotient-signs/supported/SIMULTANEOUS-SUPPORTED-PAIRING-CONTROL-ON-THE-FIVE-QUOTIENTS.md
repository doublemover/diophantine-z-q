# Simultaneous control of the supported pairing tests on all five elliptic quotients

Keep the three-factor family 48ae5e44, its pointed 4-cover and all
local squared cells ae867ee0, and the five literal elliptic quotient
maps of adb654f1. Use the ordered roots s,t,u and coefficients
a,b,c from those proofs; in particular \(u=1/2399\) and \(s<0<t,u\).
The first two supports and the already pointed 4-cover are fixed
throughout; only the last clone \(q_c\) is chosen. We prove that all
the pairings of the five exact quotient marks **against their
computed coefficient-supported subspaces** can be set to zero
simultaneously, not merely one at a time. The already pointed
\(E_{ab}\) mark is in the whole radical. For each other quotient
only the supported subspace is tested. This is not a full Selmer
lift on the four other quotients, a global point, or a Lean result.

## 1. A product identity for the four literal conic tangents

For any pair of factors with coefficients \(d_i,d_j\), roots
\(r_i,r_j\), and ordinates \(U_i,U_j\), its pair cover \(C_{ij}\)
is the diagonal genus-one intersection
\(W^2-r_i Z^2=d_iU_i^2,\ W^2-r_j Z^2=d_jU_j^2\).
It has all four conic projections forgetting one of its four
coordinates. Denote chosen tangent linear forms, pulled back to
that same projective model, as follows:
 
* \(L_i\) and \(L_j\) for the two original factor conics;
* \(A_{ij}\) for the direct difference conic
  \(d_iU_i^2-d_jU_j^2=(r_j-r_i)Z^2\);
* \(B_{ij}\) for the weighted difference conic
  \(r_jd_iU_i^2-r_id_jU_j^2=(r_j-r_i)W^2\).

Each conic is nonsingular, with an actual rational point by the
Hasse condition from the everywhere local \(C_3\). Choose one tangent
for each, using the **same** \(L_i\) wherever that conic recurs.
The degree-two projection has deck involution given by flipping
the omitted coordinate; the tangent cut pulled back to \(C_{ij}\)
is twice the degree-two divisor \(D_i\) of the fiber above the
chosen conic point (use distinct subscripts for the four fibers).
On the geometric genus-one curve pick an origin. All four sign
involutions have fixed points (their respective zero coordinate
cuts), so are of the form \(P\mapsto R_i-P\). Any two distinct
ones differ by one of the four distinct rational 2-torsion
translations, as is also seen from the actual degree-four
even-sign deck of the pair map. Thus the four \(R_i\) form a
coset of the full 2-torsion and \(\sum_i R_i=4R_1\).
The degree-two fiber classes correspond to \(R_i\) in
\(\mathrm{Pic}^2\), and each doubled fiber is a hyperplane cut.
Consequently \(\sum_i D_i\) is linearly equivalent to twice
the hyperplane class, over the algebraic closure and over Q:
the divisor difference is rational and its principal function
descends by Hilbert 90. Therefore
\[
        A_{ij} B_{ij} L_i L_j
          = \text{a rational constant times a square}
          \quad\text{on }C_{ij} ,
\]
after dividing by the fourth power of any nonzero linear section.
In a global product of local Hilbert symbols against the same
rational second argument, that constant and the fourth power
contribute + by reciprocity. This is an exact function/divisor
identity; it does not require a rational point on \(C_{ij}\).

## 2. The cubic and inverted supported tests have literal identities

Write \(P_X(U)\) for the additive Cassels bit of the actual mark
against the vector \(U\) on quotient \(X\). Use
\[
             U=(a,1,a),\qquad V=(1,a,a).
\]
They are in every quotient's computed supported subgroup where used
below. In the ordinary conic tangent formula
[Shukla--Stoll, (3.10)](https://arxiv.org/pdf/2302.01640),
the three conics for \(E_{ij}\), ordered \(0,r_i,r_j\), have
tangents \((A_{ij},L_j,L_i)\). For the cubic quotient, ordered
\(s,t,u\), the underlying two-cover has coordinates
\((U_a,U_b,U_c,Z)\) obtained by forgetting W in \(C_3\).
Its three tangents are \((A_{bc},A_{ac},A_{ab})\).
For the inverted quotient the two-cover has coordinates
\((U_a,U_b,U_c,W)\) obtained by forgetting Z; its three tangents
are \((B_{bc},B_{ac},B_{ab})\). To verify this last model,
\(x=-abc\,stu/w^2\); subtracting its first root yields
\(abc\,tu\cdot a (U_a/w)^2\), and the analogous expressions
for the other two roots give precisely the weighted difference
conics in §1 by eliminating the remaining involution coordinate.
Any rational coordinate factors in choosing those tangent forms
produce only global Hilbert reciprocity constants. A common
projective scaling cancels in each selected two-tangent product.

At every place evaluate all these tangent expressions on
the same local \(C_3\) point, away from the finitely many
tangent zeroes. This is permissible because the smooth local
curve has local points and an open coordinate disk, so avoidance
of finitely many points is possible. The literal tangent products
then give
\[
\begin{aligned}
 P_{\rm abc}(V)&=P_{ac}(U)+P_{ab}(U),\\
 P_{\rm inv}(U)&=P_{\rm abc}(U)+P_{ac}(V),\\
 P_{\rm inv}(V)&=P_{\rm abc}(V)+P_{ac}(V)+P_{ab}(V).
\end{aligned}
\]
The first formula cancels the shared original factor tangent
\(L_a\) in \(P_{ac}(U)+P_{ab}(U)\). In the second, replace
the two weighted difference factors by direct difference factors
and their original tangent pairs using §1: the ratio modulo
constant squares becomes \(L_aL_c\). In the third the ratio
becomes \(L_bL_c\), product of the two original-pair ratios
\(L_aL_c\) and \(L_aL_b\). This is why the apparently extra
three pairing tests are not independent unknown constants.

From the exact masks in adb654f1, on \(E_{ac}\) the mark and U,V
generate its 3-dimensional supported space; on \(E_{\rm abc}\)
the mark and U,V do as well (the remaining generator equals
mark plus V). The inverted supported space is just U,V.
On \(E_{bc}\) only its already computed single extra test is
needed, and every \(E_{ab}\) test is zero by its pointed lift.
It therefore suffices to set \(P_{ac}(U),P_{ac}(V),P_{\rm abc}(U)\)
and the E_bc test to zero.

## 3. The last-prime Frobenius can realize the required three bits together

First choose the exact quartic phase at 2399 which makes the
E_bc test zero by adb654f1. Both branches there keep all old
conditions and the same first two factors; a nonnumerical
admissible reference prime in the successful branch suffices.

For each of the remaining three tests take normalized cocycles
by subtracting the torsion row at the moving \(q_c\); the relevant
cocycles then vanish locally at \(q_c\). On \(E_{ac}\), the
normalized mark is \((u,a(u-s),au(u-s))\). On \(E_{\rm abc}\)
it is
\[
              (a(u-s),\ b(u-t),\ ab(u-s)(u-t)).
\]
For the cubic verify the subtraction directly: its raw mark is
\((bc,ac,ab)\), and its u-root torsion row for \(D=abc\) is
\((D(u-s),D(u-t),(u-s)(u-t))\).
The two fixed probes U,V are already normalized where used
because the first factor a is a square at each of the two
third-support primes (the actual s−u signs on that pair
are +). They represent \(\chi_a\) times the middle or first
torsion direction. Thus the three Weil cups, in the order
above, are
\[
    \chi_{a(u-s)}\cup\chi_a,\qquad
    \chi_{u}\cup\chi_a,\qquad
    \chi_{b(u-t)}\cup\chi_a.
\]
The corresponding classes are honest global Selmer classes by
the supported computations and the literal local cover.
Their cups have global primitives unramified outside the fixed
bad set (B, old a and b, the final pilot, and infinity)
as in [Smith, Theorem 3.2 proof (3.3)](https://arxiv.org/pdf/1607.07860).
Use that result separately on the three actual fixed models twisted
by \(q_c\): clone ratios are squares at the fixed bad places,
all normalized rows vanish at the varying prime, and the three
governing fields can be included in one fixed compositum.

Over \(G=\mathbf Q(i)\) lift inertia \(I\) at \(p_a\) with
\(\chi_a(I)=1\). Its image is central on the full order/ray
governor for \(q_c\), since \(p_a\) is stripped from the order
anchor and only its abelian ray layer is ramified. For
\(g\in G_G\), evaluation of the three cup primitives on
\([I,g]\) yields
\[
                \bigl(\chi_{u-s}(g),\,\chi_u(g),\,
                                    \chi_{b(u-t)}(g)\bigr).
\]
For example the two \(a\) contributions cancel in the first
primitive's commutator; the other fixed radicands are units
at \(p_a\). These three quadratic classes are independent
over \(G\): u has class 2399, and the actual \(p_b\) bits are
\(\chi_u=+\), \(\chi_{u-s}=-\), distinguishing the first
two (both are positive rational classes). The third has
odd valuation at \(p_b\), whereas the first two are units
there. Thus the commutators attain all three prescribed bits.
They fix the E_bc quartic governing layer because that layer
is abelian over G. They also fix the original order/ray field
and all the involved quadratic cocycle fields. Attach the
desired central shift to the already chosen admissible
reference Frobenius. The same degree-one Chebotarev and the
original relative independent Gaussian rays, medium
Brun--Titchmarsh and large lattice tails apply: the extra
fields ramify only at the already fixed support, with no
new rational prime for the tails.

We can therefore choose a single \(q_c\) simultaneously
passing the exact four independent supported tests.
The three tangent identities show that the other three
computed supported tests then vanish automatically. All
previous original cells and the joint real index condition
are retained. The result **does not** assert that the other
four marks are in the full pairing radicals, that their
curves have rational points, or that independent rational
points on quotient curves could be recombined without
further finite and global compatibility checks.
