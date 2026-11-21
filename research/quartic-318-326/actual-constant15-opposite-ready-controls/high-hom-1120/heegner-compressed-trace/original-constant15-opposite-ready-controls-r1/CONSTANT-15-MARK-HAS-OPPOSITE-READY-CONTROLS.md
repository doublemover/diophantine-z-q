# Opposite Ready controls for the constant-conductor-15 mark

This is a finite comparison of **two standalone numerical Ready poles**.
Neither comes from the original linked cyclic scalar or three-detector
source. The comparison is on the exact constant-conductor receiver in
[RC's fixed-model packet](../../../rc-native-helper-20261120/ct-original-constant15-marked-receiver-r1/CONSTANT-15-MARK-AND-UNIFORM-29-SOURCE-GATE.md),
note SHA 2a850c80dcbc7bfd313cf140a274e794bd07d1777bbd6ab870f5b1e566993274.
It does not compare the original unrestricted PointPair on the negative
pole: that pole fails this receiver and might still have a PointPair
via a different relation between its two mark parameters.

## 1. Same local framework, different global answers

Use \(\beta=17\) and write \(17c^2+\theta e^2=1\) with
\(b=(17c)^2\), so \(b/17=17c^2\) and
\([1-b/17]=\theta\). Consider the following two exact rows:

| \(\theta\) | \((c,e)\) | \(b\) | \((v_2,v_3,v_{17})(b)\) | \(d=17\theta\) |
|---|---|---|---|---|
| 409 | \((24,1)/101\) | \(166464/10201\) | \((6,2,2)\) | 6953 |
| 769 | \((36,1)/151\) | \(374544/22801\) | \((4,4,2)\) | 13073 |

The rational square \(b\) has square denominator, \(0<b<17\),
and the exact required positive local depths, so each is literally
Ready as a rational number. Both \(\theta\)'s are prime,
\(1\bmod24\), square at 5 and 17, with \(17\) square at
\(\theta\). Both \(d\)'s are \(17\bmod24\), prime to 15, and
nonsquare mod 5. The fixed isogeny and its dual are
\[
 \varphi:J_d:y^2=x(x+16d)(x+25d)\longrightarrow
             J'_d:y^2=x(x-d)(x-81d),\qquad \psi=\widehat\varphi .
\]
Here \(\kappa_\varphi\) reads the scalar \(x\)-class on \(J'_d\)
and \(\kappa_\psi\) the scalar \(x\)-class on \(J_d\).
The genus-one receiver requires \(\kappa_\varphi=\theta\),
equivalently \(\beta\) by translating with the torsion class \(d\).

In fact both controls can be placed in the **same p29 type as the
literal cyclic source**, without altering either pair of global
squareclasses. In each row let \((C,1)/D\) be the displayed conic
point. The other intersection with the line of slope \(m\) has
\[
 c'=\frac{C(\theta m^2-17)-2\theta m}{D(17+\theta m^2)},
 \qquad
 e'=\frac{17-\theta m^2-34Cm}{D(17+\theta m^2)} .
\]
Use exactly \(m=154224\) and \(44064\) in order. The replay checks
the same readiness depths, \(v_{29}(c')=-1\), and
\(1-17c'^2\) and \(25-153c'^2\) each of depth \(-2\) with
nonsquare stripped units. (Their unit pairs are \((26,2)\) and
\((27,11)\) respectively.) These are the same depth parity and
squareclass obstruction to the source's special \(e_{\rm receiver}=1\)
test, not equal rational units or cyclic origin.
In both rows \((17/29)=(\theta/29)=-1\) and \((d/29)=+1\).
Any rational point on the constant-model cover still transports
to either representative on its same norm conic.

## 2. The exact two-isogeny Selmer dimensions coincide

In the orientation above the kernel classes at each ramified
odd prime \(p\mid d\), away from 2,3,5, are \(\{1,d\}\) for
\(\varphi\) and \(\{1,-d\}\) for \(\psi\).
For example, on \(J'_d\) a coordinate of valuation one is \(x=dz\)
with unit \(z\); because the cubic has the factor \(d^3\), the
reduced equation forces \(z\equiv1\) or \(81\) (hence square).
On \(J_d\) the possible units are \(-16,-25\) instead. Other
valuations yield the square class, by taking the nearest unit
factors in the same cubic. The displayed classes are attained
by torsion. At good odd primes outside \(2\cdot3\cdot5d\)
the isogeny Kummer image is the full unramified order-two
subgroup, since the finite-field isogeny has rational kernel of
size two and the two curves have the same number of points.

Thus \(\operatorname{Sel}^{\varphi}\) is supported on positive
classes dividing \(3d\), and \(\operatorname{Sel}^{\psi}\) on
signed classes dividing \(2\cdot5d\). These supports also follow
directly from the scalar Kummer quartic
\(z^2=e u^4+a u^2v^2+(b/e)v^4\) on
\(y^2=x(x^2+ax+b)\), or the local valuation argument away
from \(b\). The two lower caps can be seen without a complete
local enumeration:

* For \(\varphi\), the row at 17 forbids 3, because
  \((3/17)=-1\), \(\theta\) is square there, and a unit class
  after stripping an allowed factor of \(d\) must be square.
  Hence the space has dimension at most two. Both
  \(d\) and \(\theta\) are admitted everywhere. For \(\theta\),
  it is a square at 2,3,5,17 and at infinity, equal to the torsion
  class \(d\) at \(\theta\) since \(17\) is square, and is an
  unramified unit elsewhere.
* On \(J_d\) the \(\psi\)-image has even valuations at 2.
  For odd valuation \(v_2(x)=k<0\) all root differences have
  depth \(k\); for \(k>4\) the total valuation is \(k+4\).
  Both are impossible. For \(k=1\) write \(x=2u\) with \(u\)
  odd: \(x(x+16d)\) has stripped unit 1 mod 8, but
  \(x+25d\equiv1+2u\pmod8\) is nonsquare. For \(k=3\),
  the first stripped product is \(u(u+2d)\equiv1+2u\),
  and the other unit is 1. This uses \(d\equiv1\bmod8\).
  The exceptional torsion coordinates have even valuations
  as well. So 2 is excluded in \(\operatorname{Sel}^{\psi}\).
  Its row at 17 forbids 5 by \((5/17)=-1\),
  with \(-1,\theta\) square there. At 3 the \(\psi\)-class
  must be square: if \(v_3(x)<0\), the two factors after
  dividing by \(x\) are square units; if \(v_3(x)>0\) the
  two nonzero root factors have square product; if \(x\) is a
  unit, the class \(x\equiv2\) gives nonsquare cubic value,
  since \(d\equiv2\pmod3\). The torsion classes are square
  there as well. The sign and 17 exponents must therefore
  coincide. This leaves dimension at most two. Both \(-d\)
  and \(-17\) really are local classes everywhere: the latter
  equals the torsion \(-d\) at 2,5,17 and infinity, is square
  at 3 and at \(\theta\), and is an unramified unit elsewhere.

Consequently the two exact dimensions are \((2,2)\) in **both**
rows, with the same described bases \((d,\theta)\) and
\((-d,-17)\). This is just the two isogeny Selmer groups, not a
claim that the whole 2-Selmer packets or Tate--Shafarevich groups
are isomorphic. If the two rational scalar image dimensions
are \(r_\varphi,r_\psi\), then
\(\operatorname{rank}J_d=r_\varphi+r_\psi-2\), since
\(\psi\varphi=[2]\), both curves have full rational
2-torsion and \(\varphi(J_d[2])=\ker\psi\).
In particular a general minimal isogeny mark certificate is
\(\operatorname{Sel}^{\varphi}=\langle d,\theta\rangle\)
and *certified algebraic rank at least*
\(\dim\operatorname{Sel}^{\psi}\), not parity alone.

## 3. Exact positive row: rank two and the original raw identities

For \(\theta=409\) there is a direct receiver point:
\[
 u=81,\qquad
 u^2-17=16\cdot409,\qquad u^2-81\cdot17=72^2 .
\]
Thus \(W=117792\) satisfies
\(W^2=409(u^2-17)(u^2-81\cdot17)\),
giving \((\theta u^2,\theta uW)=(2683449,3902331168)\) on \(J'_d\)
with the required \(\theta\)-class. The point
\((-134657,11111472)\) on \(J_d\) has \(x=-17\cdot89^2\),
giving its other non-torsion scalar class \(-17\).
Together with the torsion classes \(d\) and \(-d\) this gives
\(r_\varphi=r_\psi=2\), hence exact rational rank two, without
an analytic rank-two theorem.

The replay also uses the companion parameter relation \(t'=3t\)
with \(t=1/81\) and receiver ordinate
\(V=eW/81^2\), and checks the *original* two rational identities
with nonzero \(s,y_1,y_2\), both for the small \(b\) and
the exact \(v_{29}(c')=-1\) representative. It is the original
PointPair contract on these standalone poles, not a shared
production index.

## 4. Exact negative row: local admission with no rational mark

For \(\theta=769\) we certify rank zero by a short rigorous exact
Mellin computation, not by an assumed parity-implies-rank statement.
The model \(J_1\) changes under \(x=4X, y=8Y+4X\) to
\(Y^2+XY=X^3+10X^2+25X\), with integral discriminant
\(3^4 5^4\), \(c_4=481\), and conductor 15.
The unique normalized level-15 weight-two form is
\[
 f(z)=\eta(z)\eta(3z)\eta(5z)\eta(15z)=\sum_{n\ge1}a_n q^n.
\]
For the eta-quotient criterion (Newman and Ligozat, presented
in [Rouse–Webb, §1](https://educ.jmu.edu/~webbjj/papers/onspacesetaQ.pdf)),
both exponent sums are 24, the character parameter 225 is a
square, and the cusp orders at the four squarefree-level cusp
denominators are all 1. The index is 24, there are four cusps
and no elliptic points, so \(X_0(15)\) has genus one; this form
is the one attached to \(J_1\). The Fricke formula for each eta
factor gives eigenvalue \(-1\) for \(W_{15}\), hence root sign
\(+1\). Both control \(d\)'s are positive fundamental
discriminants prime to 15 with
\(\chi_d(-15)=(-1)\cdot(-1)=+1\), so their root signs are even
and their conductors are \(15d^2\).

For \(d=13073\), split the weight-two Mellin integral at
\(1/\sqrt{15d^2}\). Its root sign makes the two halves equal:
\[
 L(J_d,1)=2\sum_{n\ge1}\frac{a_n\chi_d(n)}n
                          e^{-2\pi n/(d\sqrt{15})}.
\]
Euler's pentagonal identity gives the exact first 100,000
coefficients by four sparse polynomial products. The exponential
ratio \(r=e^{-2\pi/(d\sqrt{15})}\) is bounded using Machin's formula,
integer-square-root brackets and a signed alternating Taylor
interval. Integer updates at scale \(10^{30}\) bound every
power, and signs are respected in summing the series.
The partial sum lies in \([783,784]/1000\).
Using \(|a_n|\le\tau(n)\sqrt n\le2n\), the entire tail is at
most \(4r^{100001}/(1-r)<132/1000\).
The exact interval actually returned by the replay is
\([652,916]/1000\), excluding zero by a wide margin.
For the analytic-to-algebraic implication, use
[Murty–Murty, Theorem 1](https://williamstein.org/sage_summer/bsd_comp/Murty-Murty-Mean_Values_of_Derivatives_of_Modular_L-Series.pdf)
for the derivative at an imaginary discriminant meeting the
Heegner hypothesis, then Gross–Zagier and
[Kolyvagin's rank-zero theorem](https://doi.org/10.1070/IM1989v032n03ABEH000779).
The latter uses the nonzero Heegner point over that auxiliary
quadratic field; no finiteness of Sha is an input.
Hence \(J_{13073}\) and its isogenous curve have rank zero.

On \(J'_d\), the largest real root \(81d\) is the only
nonzero 2-torsion point that could have a rational half:
for the other two roots some root difference is negative.
Halving \(81d\) would require the nonsquare \(81d\) to be
square. Thus the 2-primary torsion is exactly \(J'_d[2]\).
Odd torsion has trivial image in the exponent-two scalar
Kummer quotient, and the torsion abscissa image is
\(\{1,d\}\). The admitted class \(769\) is therefore not
rational; the exact constant-15 receiver has no rational point
for either negative representative. This is not a statement
about general original PointPairs.

## 5. Fixed-source and distribution boundary

The original selected helpers \(q_0,R,s\) alter auxiliary
twists, not \(d=\beta\theta\) of this constant receiver after
the pole is fixed. They cannot tune its rational \(x\)-image.
The isogeny above is balanced in the sense of
[Smith, Definition 1.6](https://arxiv.org/html/2503.17619v1);
his Theorem 1.7 covers its twist family but gives distribution
of the full 2-primary **Selmer corank** as the twist parameter
varies, not algebraic rank nor this marked class at an
individual pole. In particular it does not certify a hit
on the same source indices. The two controls show why neither
the minimal isogeny-Selmer dimensions, the sign, all-local
admission, nor the shared p29 type together imply that a fixed
Ready-pole receiver has a point.

Reproduce the arithmetic (Python 3 standard library, about 9 s):
```
python3 -B check_constant15_ready_controls.py | cmp - EXACT-CONSTANT15-OPPOSITE-READY-CONTROLS.json
sha256sum -c SHA256SUMS
```
