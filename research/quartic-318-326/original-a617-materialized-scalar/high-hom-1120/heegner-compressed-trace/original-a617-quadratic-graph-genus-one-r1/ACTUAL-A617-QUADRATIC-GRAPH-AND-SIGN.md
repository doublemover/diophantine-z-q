# An everywhere local degree-two graph receiver on an admissible \(a=617\) scalar branch

This proof works on the **scalar pole** of a permitted original input
\(a=617\), not on the previously fixed \(a=0\) scalar and not on the
other three poles. It gives a new smooth genus-one curve whose
\(\mathbf Q\)-points give the exact same-pole PointPair. The original
elliptic-index construction can make this curve everywhere locally
soluble without an admission norm or test at any unseen prime of
\(\theta\), and can realize opposite root numbers on its Jacobian
by changing a finite local phase. Neither a global rational point
nor rank positivity is inferred from these facts.

## 1. A literal source squareclass that allows the new ramified graph

From the [original source scalar coefficient](../../../rc-native-helper-20261120/ct-original-scalar-union-thinness-r1/SCALAR-RETUNING-DOES-NOT-THICKEN-THE-MARK.md)
put \(z_a=2a+1\) and write its raw \(R\) as \(4g_1g_2g_3g_4\), where
\[
 g_1=(3723z_a^2-2401)/2,\quad
 g_2=(3723z_a^2-1)/2,\quad
 g_3=7446z_a^2-1,\quad g_4=119136z_a^2+343.
\]
The raw scalar is
\[
 \beta_{\rm raw}=187R/4,\quad K=1+2448\beta_{\rm raw},\quad
 \mu=\beta_{\rm raw}(12W/K)^2,\quad \delta=1-\mu .
\]
On the actual input \(a=617\), \(z_a=1235\), the four exact
factorizations are
\[
 (g_1,g_2,g_3,g_4)=(2839205137,\ 11\cdot601\cdot429467,\
                     359\cdot31634611,\ 359\cdot506153777).
\]
Consequently \(\beta_{\rm raw}=(11\cdot359)^2\beta\), with
\[
 \beta=199477972060937362209233596181078921
      =17\cdot601\cdot429467\cdot2839205137\cdot31634611\cdot506153777 .
\]
The replay verifies the primality and exact identities. Crucially,
\[
 \beta=x_0^2+2y_0^2,\quad
 x_0=362538667625927811,\quad y_0=184450110513594440 .
\]
Thus this actual first squareclass is a norm from
\(\mathbf Q(\sqrt{-2})\). This is not true for \(a=0\), since
its 661 factor has symbol \((-2/661)=-1\) and odd depth.

A useful distinction is that the \(+\sqrt2\) norm alternative
cannot work for **any** integer \(a\): \(g_3\equiv5\bmod8\)
has \((2/g_3)=-1\); every odd-depth nonsplit prime of \(g_3\)
is disjoint from the other factors and 11,17.
Indeed \(\gcd(g_2,g_3)=1\),
\(\gcd(2g_1,g_3)\mid4801\), \(\gcd(g_3,g_4)\mid359\);
4801 and 359 are both primes split in \(\mathbf Q(\sqrt2)\).
Also \(g_3\not\equiv0\bmod17\), and at 11 its vanishing
would require \(z_a^2=-1\bmod11\). Thus the split choice
of quadratic norm for the graph is substantive.

## 2. Exact degree-two graph and same-pole back-map

Use the explicit first-mark family from
[the constant-15 receiver](../../../rc-native-helper-20261120/ct-original-constant15-marked-receiver-r1/CONSTANT-15-MARK-AND-UNIFORM-29-SOURCE-GATE.md).
It is convenient to put its full mark formulas in homogeneous
coordinates. For \(t=[T:S]\in\mathbf P^1(\mathbf Q)\) let
\[
 F(T,S)=(S^2-\beta T^2)(S^2-9\beta T^2),\quad
 A(T,S)=S^2+3\beta T^2,\quad D(T,S)=\beta F(T,S) .
\]
On \(E_D:y^2=x(x-D)(x+3D)\) the exact point is
\[
 X=\beta A^2,\qquad Y=8\beta^2 A\,ST(S^2-3\beta T^2) .
\]
Multiplying out the three factors verifies this, including
\(S=0\) or \(T=0\); zero ordinates are allowed in the literal
PointPair. Since \(\beta\) is nonsquare positive, \(F\ne0\)
and \(A>0\) on the whole rational projective line.

Set \(t_0=1/(3x_0)\), \(z=2y_0/x_0\),
\(\lambda=\beta t_0^2=(z^2+2)/18\).
We work on the source parameter \(t=t_0 v\), and use the
following affine polynomial formulas with their evident
homogenizations in \(v=[V_1:V_0]\):
\[
 \begin{split}
 W_0&=-2(z^2+2)v+4-z^2,\quad U_0=(z+4)(v-1),\\
 P&=W_0^2+(z^2+2)U_0^2-2zW_0U_0,\quad
 Q=W_0^2-(z^2+2)U_0^2,\\
 Z&=-z(W_0^2+(z^2+2)U_0^2)+2(z^2+2)W_0U_0.
 \end{split}
\]
The graph parameter is \(t'=[t_0P:Q]\).
It parametrizes \((Z/Q)^2-18\beta(t_0P/Q)^2=-2\);
this is the conic through \((z,t_0)\) given above,
with parameter \(W_0/U_0\) on the lines through that point.
The map to \(t'\) has degree two. At \(v=1\), \(P=Q\ne0\)
and \(Z/Q=-z\), so \(t'=t=t_0\).
Writing \(s=\sqrt{\beta}\), at \(t=\pm1/(3s)\) the matched
target point has \(t'=\pm1/s\), \(Z/Q=4\).
At the other pair of target points \(t'=\pm1/s\), \(Z/Q=-4\),
their inverse images are two conjugate points over
\(\mathbf Q(s)\). Conversely these are all four unramified
inverse images of \(t'=\pm1/s\) on the conic.
The 2:1 conic projection to \(t'\) ramifies exactly over
\(t'=\pm1/(3s)\).

Put
\[
 L=\frac{Q^2-\lambda P^2}{1-9\lambda v^2},\qquad
 H=-\tfrac12(1-\lambda v^2)L .
\]
The indicated division is exact of binary forms and \(L\)
is quadratic. The resulting smooth genus-one receiver is
\[
                         \mathcal C_\delta:\quad Y_0^2=\delta H(v).
\]
Indeed the replay verifies the following nonzero discriminant,
with the same rational \(z\):
\[
 \operatorname{disc} H=\frac{1024}{729}z^{16}(z-4)^2(z+4)^8
 (z^2+2)^6 (z^2-40z-32)^2(7z^3+16z^2+32z+32)^2 .
\]
All four geometric branch points are distinct and lie over the
same quadratic field \(\mathbf Q(s)\), with two nonrational
conjugate pairs as described. The Jacobian therefore has full
rational 2-torsion (the three unordered partitions into pairs
are fixed by a simultaneous flip of the two conjugate pairs).
For \(\delta=1\), \(v=1\) gives the rational point
\(Y_0=z^3(z^2-16)/2\ne0\).

For a **rational point of the actual \(\mathcal C_\delta\)**,
use the homogeneous \(t,t'\) given above. The exact identity is
\[
 \delta F(t)F(t')
   =\left[Z\,(V_0^2-9\lambda V_1^2)\,Y_0\right]^2 .
\]
Here \(Q^2-9\lambda P^2=-Z^2/2\) supplies the removed
target branch pair and \(Q^2-\lambda P^2=(V_0^2-9\lambda V_1^2)L\)
supplies the shared pair.
Thus \(D(t')=\delta D(t)\rho^2\) for the nonzero rational
\(\rho=Z(V_0^2-9\lambda V_1^2)Y_0/(\delta F(t))\).
The use of binary forms covers \(v=\infty\) without losing a
possible rational point.

Write \(\mu=\beta c^2\) with
\(c=(11\cdot359)\,12W/K\), and \(B=17b=\beta(17c)^2\)
for the literal scalar pole \(b=17\mu\). Divide the second marked
point's coordinates by \(\rho^2,\rho^3\); it is on \(E_{\delta D(t)}\).
The scalings
\[
 \lambda_0=17c/A(t),\qquad \lambda_1=17c\rho/A(t'),\qquad
 T=D(t)\lambda_0^2,\qquad s_{\rm out}=B\lambda_0/\lambda_1
\]
give the two literal PointPair abscissae \(B,Bs_{\rm out}^2\)
and the two curve parameters \(T,\ TB^2\delta\).
In particular \(s_{\rm out}\ne0\), the pole is unchanged, and
there is no demand for a second independently selected rank.

## 3. Actual finite index compatibility and all places

Let \(\mathcal B\) consist of primes in the denominator of \(z\)
and the numerator factors of the displayed discriminant, together
with \(2,3\). It is a fixed finite set, not a collection of unseen
\(\theta\)-primes. The finite replay proves:
* The only members \(p\le64\) are \(2,3,5,13,17,47\).
  At 5,13,47 the value \(\beta\) is a square unit.
* Outside \(2,3,\beta\), \(\mathcal B\) is disjoint from
  the primes of \(R K (K^2-144\beta_{\rm raw})\).
  This is an exact integer gcd of the displayed factors,
  not a factorization of any source value of \(\delta\).

We can prepare \(h_b\) on the actual original source curve
\[
 y^2=x^3-(3-\sqrt2)^2x,\qquad P_0=(1+\sqrt2,2\sqrt2),
\]
so that its two arms are formal at every prescribed good odd
place, to any fixed finite depth, and \(64\mid h_b\).
This uses multiples of the finite residue orders and one extra
power of each desired prime as in
[the actual formal index construction](../../../joined-work-20261120/rc-linked-scalar-variable-index-auxiliary-r1/ACTUAL-VARIABLE-SCALAR-AUXILIARY-PLACE-INDEPENDENCE.md).
Use the same Lucas label \(s_{\rm lab}=1+i\) with
\(i=m h_b\), and take \(6^{15}3^{65536}\mid m\).
At the primes dividing \(2\cdot3\cdot17\cdot R\), take \(m\)
sufficiently divisible to get \(W\) a unit congruent to one
(and \(h_b\) sufficiently deep compared with \(v_p(R)\)).
This follows from \(U=-2t_{\rm form}+O(t_{\rm form}^3)\) on
the odd formal chart, the original dyadic norm depth for
\(64\mid h_b\), and \(v_p(Q_{\rm pack})=2v_p(m)-15v_p(R)\).
In particular the square denominator and dyadic, 3-adic,
17-adic Ready scalar conditions are retained:
\(\beta_{\rm raw}\equiv1\bmod8,\ \equiv2\bmod3\),
and \(\beta_{\rm raw}/17\equiv1\bmod17\); \(W\) stays a
unit at the full raw first support. At these places
\(\delta\) is a local square (at 2, \(\mu\) has depth at
least four; at 3, its depth at least two).
The prime 7 is not needed by any of these formal conditions.

At any \(p>64\) in \(\mathcal B\) not dividing
\(2\cdot3\cdot\beta\), exact formal division gives
\[
 W\equiv1+m^4/R^{29}\pmod p,\qquad
 \delta\equiv G_p(m):=
      1-\beta_{\rm raw}
          \left(\frac{12(1+m^4/R^{29})}{K}\right)^2 \pmod p.
\]
The same formula applies at 5,13,47. The degree-eight
polynomial at the large primes has eight distinct geometric
roots: excluding \(p\mid 2\cdot3\cdot\beta_{\rm raw} RK\)
makes its two quartic factors distinct and separable except
possibly at \(m=0\), and exclusion of
\(p\mid K^2-144\beta_{\rm raw}\) prevents that zero.
The quadratic [Weil character bound](https://doi.org/10.1073/pnas.34.5.204)
is \(7\sqrt p\), less than \(p-8\) for \(p>64\).
Hence both nonzero signs occur and we can prescribe the
square unit sign at every such prime. For the remaining
small places the exact choices are
\[
 (p,m\bmod p,\delta\bmod p)=(5,0,2),\
      (13,0,4)\ \text{or }(13,1,5),\quad (47,2,34).
\]
Here 5 and the second 13 mode are nonsquare; 47 is square.
In particular both source branches have **nonsquare**
global \(\delta\) because it is a nonsquare unit at 5.
All these conditions on \(m\) coexist by CRT, and labels are
then fixed. The original
\(\texttt{JointSmallPrimePreparation318.adjust_center}\)
selects a positive later \(h\) on a sufficiently deep congruence
progression through \(h_b\), preserving the scalar conditions
by continuity at the nonzero \(h_b\)-chart. It supplies the
original guard and strict real margin;
\(\texttt{PreparedIntegerSource318.scalar_domain}\)
then gives \(0<b<17\) at the literal final \(h\).
The index \(i=m h_b\) stays fixed in this step; we neither
require \(h\mid i\) at the final center nor change any value
of \(W\) to its residue. This is an existential finite-index
construction, not a numerical materialization of all orders
or of the new scalar's reduced numerator.

For either resulting scalar, \(\mathcal C_\delta\) is now
locally soluble at **every** place. At a square-\(\delta\)
place use the \(v=1\) rational baseline point, scaled by
\(\sqrt\delta\). At a place where \(\beta\) is a square
there is a rational branch point in the first quadratic
\(1-\lambda v^2\), irrespective of the sign of \(\delta\).
In particular this accounts for all odd-depth primes of
the literal \(\delta\): at any pole of \(c\), \(v_p(\delta)\)
is even; and if the depth is positive odd then
\(1\equiv\beta c^2\bmod p\), so \(\beta\) is a square
in \(\mathbf Q_p\) (the primes over \(2\beta\) were already
handled by preparation). This also accounts for nonsquare
small modes 5 and 13. Finally outside \(\mathcal B\) at a
remaining odd place, remove the even valuation of \(\delta\)
by a square. The resulting unit twist has smooth genus-one
reduction and a finite-field point by Hasse, which lifts.

## 4. Exact sign flexibility, not a rank claim

The Jacobian for the \(\delta\)-curve is the quadratic twist
by \([\delta]\) of that for \(\delta=1\): the binary quartic
invariants scale by \(\delta^2,\delta^3\).
At 13 the literal rational \(I,J\) of \(H\) are both units
and \(v_{13}(4I^3-J^2)=2\) by the exact replay.
The short Jacobian \(y^2=x^3-27Ix-27J\) therefore has
multiplicative \(I_2\) there, using its unit \(c_4\).
The unramified nonsquare twist at 13 switches splitness
and flips the local sign. All other fixed bad local twist
classes are the same in the two preparations. New odd
ramified twist primes, all from good reduction on the
fixed Jacobian, contribute \((-1/p)\) by the tame quadratic
twist local formula (see [Bisatt, §2](https://arxiv.org/pdf/1711.09961)).
Their product is \(+1\) since the positive squarefree
\(\theta\) is a square in \(\mathbf Q_2\), is odd,
and is coprime to the fixed bad places. Thus the global
signs of the two branches are opposite, although we do not
label which is negative. By
[Dokchitser–Dokchitser, Theorem 1.8](https://arxiv.org/pdf/0906.1815)
the negative branch has odd 2-infinity Selmer corank
(the Jacobian has rational 2-isogenies). This is not an
unconditional Mordell–Weil rank or a rational point.
The exact computation also gives \(v_{13}(j)=-2\) and
\(v_{47}(j)=-2\); in particular this is not a geometric
isogeny transplant from the earlier constant-15 or
constant-40 receivers (whose \(j\)-invariants are integral
at those places).

A precise remaining rank-positive route is to prove, on a
single allowed scalar in the negative branch, actual rank
one and finite \(\operatorname{Sel}_2\) dimension at most
three. The genus-one binary quartic has its rational
degree-two divisor and hence its natural full [2]-covering
of the Jacobian; everywhere local solubility puts that
class in \(\operatorname{Sel}_2\). Full rational 2-torsion
and rank one would fill the stated small finite group with
rational classes. Neither rank nor that dimension bound
follows from a finite character selection or from twist
density in an unconditioned family. No such theorem is
applied to the thin original elliptic-index values here.

    python3 -B check_a617_quadratic_graph.py | cmp - EXACT-A617-GRAPH.json
    sha256sum -c SHA256SUMS
