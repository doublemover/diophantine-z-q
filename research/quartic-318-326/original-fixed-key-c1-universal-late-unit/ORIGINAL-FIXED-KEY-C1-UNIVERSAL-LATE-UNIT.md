# A universal late-unit proof on the literal C1 fibre without the dense determinant

Keep the original \(a=0\) archived labels, shifted Padé denominator
and exact late anchor \(J\). For the actual C1 alternate fibre,
we prove \((J-1)\mathscr D J\) is nonzero at **every** geometric
point, even before removing the bounded base-exception support.
The calculation first compresses the special fibre to at most
twelve explicit reduced candidates, then treats its one surviving
translated-origin cluster exactly in characteristic zero.
It uses no division polynomial of degree \(n_1^2\) and does not
extend to C2, a global branch resolution, or an arithmetic
detector witness.

## 1. Exact label arithmetic compresses the degenerate place

Use the earlier quotient by \(E[2]\):
\[
       X=[2](P-P_*),\quad Z=X+T_*,\quad T_*=[2]P_*,
       \qquad R(P)=\bar R(Z)=x(Z)/y(Z).
\]
Here \(P_*\) is the literal unit-index point.
The exact C1 quotient is
\(x([n_1]X)^2=-25D/39\), where
\(D=(3-\sqrt2)^2\) on the named arm.
At the already used place over 13 its four targets
\([n_1]X\) are formal: each \(x\)-value has depth \(-1/2\).
Thus for every characteristic-zero point on the
unfiltered fibre, reduction satisfies \([n_1]\bar X=O\)
and
\[
             [n_1]\bar Z=\overline{T_*}.
\]
The latter point has exact order 15 in
\(\mathbf F_{169}\), as replayed below.
Bars denote reduction in the algebraic residue field.

The actual \(n_1\) is odd and is \(1\bmod15\).
The old Lucas recurrence gives the exact congruences
\[
       n_3\equiv0\pmod {n_1},\qquad
       n_2\equiv-1\pmod {n_1}.
\]
For the first, \(k_0=2(n_1-2)\) is even, so
\(U_{n_1}(k_0)\equiv0\bmod n_1\);
the denominator \(n_1-2\) is coprime to \(n_1\).
For the second, \(k_0+1\equiv3\bmod4\) since \(n_1\) is
odd, and the Lucas sequence modulo \(n_1\) has period
\(0,1,0,-1\).
In addition the actual \(n_1,n_2,n_3\) are
\((1,-1,1)\) modulo both 15 and 13, by the pinned
finite replay. Hence over the residue field
\[
       [n_1]\bar Z=[n_3]\bar Z=\overline{T_*},
                         \qquad [n_2]\bar Z=-\bar Z .   \tag{1}
\]
The point \(\bar Z\) has odd order because \(n_1\) is odd
and \([n_1]\bar Z\) has odd order 15. It is not the
identity. In particular none of the points in (1), or
\(\bar Z\) itself, is 2-torsion. Both \(\bar R\) and
its denominator are units in all these evaluations:
its only zeros and poles are at 2-torsion or the identity.

Work now on the elliptic quotient, using its invariant
derivation \(D_E=2y\partial_x+(3x^2-D)\partial_y\), and
put
\[
      \rho=\frac{D_E\bar R}{\bar R}
                      =-\frac{x^2+D}{y},
      \qquad a=\bar R(\overline{T_*})/\bar R(\bar Z).
\]
Thus \(a\ne0\). By (1) the reduced primary tuple is
\((a,-1,a)\). Its invariant differentiated tuple at
the same point is
\[
        \bigl(a(\rho(\overline{T_*})-\rho(\bar Z)),
                 0,\ a(\rho(\overline{T_*})-\rho(\bar Z))\bigr).
\]
Indeed for a primary quotient the pulled-back
invariant derivative of the numerator has the factor
\(n_i\), and its reduction is \(\epsilon_i\) modulo 13;
\(\bar R\) is odd and \(D_E\bar R\) even.
This is a derivative at the **point**, not a claim the
relations (1) hold identically in a nearby curve chart.
The original \(\mathscr D\) differs by a nonzero factor
2 on functions pulled back by \([2]\).
Substitution in the literal \(J\) and differentiation
therefore give, up to that unit factor on the derivative,
\[
 \begin{split}
       J-1 &= F(a)=a^2(a-1)(a-2),\\
       D_E J&=F'(a)a\bigl(\rho(\overline{T_*})-\rho(\bar Z)\bigr),
                   \quad F'(a)=a(4a^2-9a+4).
 \end{split}                                                   \tag{2}
\]
Both expressions are regular at all reduction points
under consideration; the identity holds in the
residue field.

As \(a\ne0\), (2) says that possible zero points lie
in just four degree-two fibres
\[
                       a=1,2,3,9
\]
or the single degree-four fibre
\(\rho(\bar Z)=\rho(\overline{T_*})\).
Here \(3,9\) are the two roots of \(4a^2-9a+4\)
in characteristic 13. This limits the remaining
special-fibre search independently of \(n_1\).

## 2. The only remaining reduced point is \(\overline{T_*}\)

In \(\mathbf F_{169}=\mathbf F_{13}[r]/(r^2-2)\)
use coordinates in the basis \(1,r\).
The exact bounded replay computes
\[
 \begin{split}
     D&=(11,7),\qquad
     \overline{T_*}=\big((12,3),(7,11)\big),\\
     \bar R(\overline{T_*})&=(9,3),\qquad
            \rho(\overline{T_*})=(10,12).
 \end{split}
\]
For each \(a\)-value let \(c=\bar R(\overline{T_*})/a\).
The \(x\)-equation is \(x^2-x/c^2-D=0\) and \(y=x/c\).
The rational points over \(\mathbf F_{169}\) are exactly:
- for \(a=1\), \(\overline{T_*}\) of order 15 and
  \(((3,3),(2,4))\) of order 30;
- for \(a=2,3,9\), none.

Nonrational points in those degree-two fibres cannot satisfy
\([n_1]\bar Z=\overline{T_*}\).
The nontrivial automorphism of the \(\bar R=x/y\) degree-two
map is \(Z\mapsto T_0-Z\), since \(R(T_0-Z)=R(Z)\)
and \(T_0=(0,0)\).
The \(\mathbf F_{169}\)-Frobenius on a nonrational
two-point fibre must exchange its two points, so sends
\(\bar Z\) to \(T_0-\bar Z\).
Applying \([n_1]\) and using oddness gives
\(T_0-\overline{T_*}=\overline{T_*}\), impossible by
order 15. This handles all nonrational sheets, without
enumerating any of their higher fields.

For the \(\rho\)-fibre write
\(y=-(x^2+D)/\rho(\overline{T_*})\).
Substitution gives a quartic in \(x\).
The replay finds **four distinct** roots over
\(\mathbf F_{169}\), so this is its full geometric
fibre. The points are \(\overline{T_*}\) and
\[
   ((0,5),(0,11)),\quad ((3,3),(11,9)),\quad
                                ((9,8),(1,11)),
\]
all three of order 30.
Every order-30 point is excluded because \(\bar Z\)
has odd order. Thus the only candidate where either
factor might vanish is
\(\bar Z=\overline{T_*}\), equivalently \(\bar X=O\).
The machine calculation is just a fixed check of
the \(169\) possible \(x\)-residues for these
quadratic/quartic equations and short group orders,
not a scan of \(E[n_1]\) or of primes.

## 3. Exact depth test for every lift of the remaining cluster

For each of the four formal targets in the C1 quotient,
there is exactly one formal \(X\) above it because
multiplication by the actual \(n_1\) is a formal
isomorphism at 13. To choose the native negative-sign
physical representative, put \(T=[2]^{-1}X\) in the
formal group and \(P=P_*+T\).
Then \(Q=[n_1]T\) has parameter depth \(1/4\),
and \(V(Q)^2=64/25\).
Since it is formal, \(V(Q)\) reduces to 1;
of the two possible signs only \(-8/5\) does so
in characteristic 13. Hence this \(P\) is an exact
negative-sign lift on the required fibre. Any other
lift is an \(E[2]\)-translate, which has the same
test because \(J\) and \(\mathscr D J\) are invariant.
Thus this local analytic calculation treats all
lifts of the sole remaining reduction cluster.

Return to the original physical curve, \(R=U/V\),
and write \(\rho_P=\mathscr D R/R\) there.
This is distinct from the doubled curve's \(\rho\)
in §1. Its actual residue at \(P_*\) is \(7+11r\),
a unit, from the original replay.
Near \(P_*\) define the exact
\[
                 L=\log([15]P)/15 .
\]
It has depth \(1/4\) as in the earlier selected
calibration: the formal shift contributes that depth
and \([15]P_*\) has depth at least 1 in the
unramified coefficient field.
Use \(b_i=n_i-\epsilon_i,\ \epsilon=(1,-1,1)\),
and \(K_1=b_3-2b_1-b_2\).
The exact valuations are
\(v(b_1),v(b_2),v(b_3)=(2,4,2)\) and
\(v(K_1)=4\), \(K_1/13^4\equiv7\).
The \(b_i\) are divisible by 15.
Thus the formal shift from \([\epsilon_i]P\)
to \([n_i]P\) has logarithm \(b_i L\)
of depth at least \(9/4\).
Its formal parameter differs from that log
by a term of valuation at least twice its depth.
The same integral Taylor estimates as before apply,
since all necessary chart denominators at
\(P\) and \([\epsilon_i]P\) are units.
The gradient of \(J\) at \((1,-1,1)\) is
\((-2,-1,1)\), so the exact leading expansion is
\[
           J(P)-1=K_1 L\,\rho_P(P)+O(v\ge9/2).
\]
Its leading depth is \(17/4<9/2\), hence it is
nonzero at every lift. This use of the valuation
does not need a common complex phase.

The derivative is tested by **direct** Taylor
expansion, not by differentiating this displayed
valuation error. Write \(R'=\mathscr D R\),
\(R''=\mathscr D^2R\). Oddness of \(R\) makes
\(R'\) even and \(R''\) odd. Applying the Taylor
expansion to \(R'\) gives
\[
 R'([n_i]P)=R'(P)+\epsilon_i R''(P)b_i L
                                      +O(v\ge 2v(b_iL)).
\]
The exact quotient derivative is
\(\mathscr D p_i=n_i R'([n_i]P)/R(P)-p_i\rho_P(P)\).
Substitute the displayed expansion and the
undifferentiated expansion of \(p_i\).
The resulting first two terms of the derivative are
\[
    \mathscr D p_i=b_i\bigl(\rho_P+L\mathscr D\rho_P\bigr)
                           +O(v\ge 2v(b_i)+1/4).
\]
For clarity the error includes the product of the
extra \(b_i\) in \(n_i\) with the first translated
increment \(b_iL\), while the squared formal-parameter
error has still larger depth. All derivatives of the
rational \(R\)-chart are integral at these good reduction
points. Since \(p_i-\epsilon_i\) has depth at least \(9/4\)
and \(\mathscr D p_i\) has depth at least 2, the
derivative of the nonlinear part of \(J\) has
depth at least \(17/4\). Hence
\[
   \mathscr D J(P)
       =K_1\bigl(\rho_P+L\mathscr D\rho_P\bigr)
                                      +O(v\ge17/4).
\]
The parenthesis is a unit: \(\rho_P\) is a unit and
the other term has positive depth. Consequently
\(\mathscr D J(P)\) has exact depth \(4\), and
\[
                       v\bigl((J-1)\mathscr D J(P)\bigr)=33/4 .
\]
This proves a characteristic-zero unit on the
remaining cluster (meaning nonzero on each geometric
component of the finite characteristic-zero algebra,
not a 13-adic valuation-zero element).

All other clusters already had both factors nonzero
modulo 13 by the compressed check, so the one-arm
C1 determinant for \((J-1)\mathscr D J\) is nonzero
on the **whole** unfiltered native shifted fibre,
and therefore also on the actual isolated-pole open.
The other coefficient arm has the same result by
conjugation. This refines rather than contradicts the
failure of the plain mod-13 gcd: its nontrivial
translated-origin cluster is exactly the part
treated in §3. No claim is made for the C2 fibre,
where \(E[n_2]\) in the reduction does not give
(1), or for the remaining adjoint or arithmetic
conditions of the full detector pair.

Exact immutable inputs:
- exact quotient and first mod-13 obstruction,
  checksum-list
  124a482494a0057da140a3064511f082894c3fb13c6d18b6099efac714c760b7;
- raw archived label/fibre congruences, checksum-list
  49ff217ef9aac2bad00fc752a68bfec1c25723821e02ac3649766abded6c3559;
- selected formal calculation, finite residues of the original
  \(R\)-chart and label-log data, checksum-list
  0e6671f5d6cd6d996cfa8c9d31dfce600176d5766610da741388430406e1d1e9.

Stdlib replay for the compressed geometric candidates:

    python3 -B replay_C1_twelve_reduction_candidates.py ../ct-original-fixed-key-C2-square-p13-first-deformation-r1/EXACT-C2-P13-FIRST-DEFORMATION.json | cmp - EXACT-C1-TWELVE-REDUCTION-CANDIDATES.json

No dense division-map expansion, other prime scan, proof build or push.
