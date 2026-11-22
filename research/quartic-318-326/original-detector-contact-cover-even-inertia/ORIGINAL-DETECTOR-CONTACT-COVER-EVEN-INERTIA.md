# Every literal detector contact cover carrying a certificate has positive genus

Keep one original detector's fixed labels, coherent source charts and
contact scale \(C_j=c_j^2\), with no modification of its fold.
The conclusion concerns algebraic families varying the literal
contact parameter on the exact source. It does **not** rule out
any rational specialization at a prepared key, a rational value
at one fixed contact, or points over positive-genus parameter
covers. It is not a new fixed-ratio test.

## 1. The five even-inertia requirements

Fix coherent \(h\) in the source chart under the original nonzero
norm guard \(H_h\ne0\) (or fix the generic coherent coefficient field).
Use the actual contact \(t\), and put
\[
 B=17b_j(t),\qquad \delta=1-b_j(t)/17,\qquad
 F(X)=X(X+1/2)(X+1)(X-1/2399)(X+32/407).
\]
The five pairwise distinct contacts \(C_jt=r\), for
\[
        r=0,\ -1/2,\ -1,\ 1/2399,\ -32/407,
\]
are simple roots of \(F\), none equal to 1. The exact
literal recurrence has been checked at all of them:
the three weights have pole orders \(1,7,25\) because
\(C_jt-1\) is a unit, the first nonzero order-seven term
has coefficient \(H_h^2\), and the uniquely dominant
real square gives \(28\cdot2^{13}=229376\) before the
trace. The trace quotient has the same pole order and
the other denominator \((C_jt-1)^3\) is a unit.
Thus both \(B\) and \(\delta\) have order \(-458751\) at
every contact. This is the **same** valuation already
used at one contact; the five-point version uses the
identical unit calculation, including the shared root
\(0\), not five independent source choices.

Let \(\pi:C\to\mathbf P^1_t\) be a finite nonconstant
contact cover, taking \(C\) to be smooth projective and
geometrically integral over its characteristic-zero
constant field. One may first extend constants to an
algebraic closure and take a component, so that \(d\)
below is its geometric degree and \(g\) is its genus.
Suppose the pulled-back raw detector equations have a
solution over the function field of \(C\). These are exactly
\[
  p^2=B(1-u)(1+3u),\qquad
  q^2=B(v^2-u\delta)(v^2+3u\delta),
\]
with \(u=e/17,\ v=s^{\rm cert}/17,\ p=p^{\rm cert},\
q=q^{\rm cert}/17\).
This includes the unrestricted positive or negative
zero-ordinate boundary \(q=0\); the proof does not
assume nonvanishing of any raw field.

At a geometric point of \(C\) lying over **any** of the
five contacts, if its ramification index \(e_{\pi}\) is odd,
the normalized valuation there has
\(\nu(B)=\nu(\delta)=-458751 e_{\pi}\), odd.
If \(u=0\) or \(\nu(u)>0\), the two first factors are
units, making the first right side have odd order. If
\(\nu(u)<0\), these factors have the same order
\(\nu(u)\), and again the first right side has odd order.
Neither of those right sides can vanish. Thus
\(\nu(u)=0\), also if \(p=0\), whose factor roots are
\(u=1,-1/3\). Then \(\nu(u\delta)\) is odd and
\(\nu(v^2)\) is even for \(v\ne0\).
Consequently the two factors in the second right side
are nonzero, and have the same order, namely the
minimum of these two distinct orders. For \(v=0\)
they are still nonzero with equal order \(\nu(u\delta)\).
The second right side has odd order and cannot be
a square or zero. This proves the necessary condition:
\[
 \text{every point over each of the five contacts has even }e_\pi.
                                                               \tag{*}
\]
It is a condition on the full geometric fibres, not
merely on the existence of one ramified point in each.
Excluding those fibre points from an affine formula
does not evade \((*)\), because the identities are in
the function field and can be tested at the omitted valuations.

## 2. Consequences for rational families of any contact degree

In a fibre of degree \(d\) satisfying \((*)\),
\(\sum e_\pi=d\) and the number of points is at most
\(d/2\). In particular \(d\) is even, and the contribution
to Riemann--Hurwitz from this fibre is at least \(d/2\).
With five separate contact fibres and nonnegative
contributions elsewhere,
\[
        2g-2=-2d+\sum_P(e_\pi(P)-1)\ \ge\ d/2 .
\]
Thus no nonconstant rational contact map \(t=t(z)\) of
**any** degree can pull back these equations to a rational
solution over the parameter line. A quadratic cover
requires genus at least two. For comparison this lower
bound is sharp for the unrestricted **raw** equation at
degree two: adjoining \(\sqrt B\) gives
\((u,v,p,q)=(0,1,\sqrt B,\sqrt B)\). Its squareclass is
\(17F(C_jt)\), with exactly the five finite simple
contacts and infinity as branch points, so its genus is
two. This comparison uses \(T=0\) and does **not** prove
sharpness for a strict positive-\(T\), \(q=0\) family.

If the **same** contact cover carries two raw certificates
at the distinct actual scales of slots 190 and 241, their
nonzero contact roots are disjoint: the normalized
nonzero roots of \(F\) have distinct rational squareclasses,
and the scales are distinct rational squares. The zero
contact is shared and counted once. Hence \((*)\) holds
in at least nine fibres. For this pair the same count gives
\(2g-2\ge(5/2)d\), or \(g\ge1+5d/4\).
This pair obstruction is for arbitrary certificate
parameters, not just the earlier simultaneous diagonal
square-root cover. It does not assert which degree-four
or higher algebraic extensions actually supply a pair.

## 3. When the family also purports to move the coherent index

The coherent variable in the actual fixed-label extension
is a point of the abelian surface
\(\mathcal A=\operatorname{Res}_{\mathbf Q(\sqrt2)/\mathbf Q}E\)
from the two original elliptic arms. A rational algebraic
family preserving those charts gives a rational map to
\(\mathcal A\), wherever its source charts are defined.
Any rational map from a rational parameter line to
an abelian variety in characteristic zero is constant:
it extends to a morphism by properness, and a nonconstant
morphism would pull a suitable invariant differential
back to a nonzero differential on \(\mathbf P^1\).
For two rational parameters use the two general rational
line directions, or regard each parameter in turn over
the algebraic closure of the other parameter's coefficient
field. Constancy in each shows the coherent point cannot
move in such a family. After fixing that coherent point,
any remaining nonconstant rational contact coordinate
varies along a parameter line, where the proved genus
obstruction applies. The same restriction works on an
open subset; missing contact or boundary fibres cannot
remove the valuation test.

This covers genuine rational algebraic parameter families
intertwining the coherent fold and its raw boundary,
while retaining the fixed labels. It says nothing about
nonalgebraic parametrizations, changing the source or
labels, positive-genus base changes, or isolated/discrete
prepared common keys. In particular the actual local
slot-292 zero-ordinate witnesses are unaffected.

Exact checksum-list bindings:
- Original literal fold recurrence and coherent source extension,
  d65124d6b78d3bbdb59e015bc44c3f90c4261b5fa92e7f517e4401e98feeb5fe.
- Independently checked all-five contact orders, shared zero,
  and actual distinct scales in the diagonal context,
  bcb6ab11e21b694762a5b358426b56235af2d04f2c5ad42757c7324dde9a195d.
- Native raw full-certificate ABI, single odd-pole obstruction
  and rational boundary conversions,
  84c2b9d027139166a220549467280337120df7c49f733d66d6c06a2fd5eb7e61.

No prime calculation, numerical key, build or remote action.
