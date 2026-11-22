# A degree-two family of scalar secants and its exact index-matching gate

This is for the original **input-zero** simultaneous four-Ready construction and the already fixed first point with \(t=18\). Neither a new source index, a primitive key, nor a rational point on any actual scalar is chosen here.

## 1. What has to occur at one and the same index

Fix the labels and their physical anchor from the simultaneous four-Ready theorem. Let \(\mathscr H\) be the set of actual indices delivered by that construction, with an admissible Gaussian key and all the original detector rows and scalar preparation. This notation is for a set of positive integers, not for an affine parameter space. At \(h\in\mathscr H\) write \(W(h)\) for the fixed native packed expression and put
\[
  L_s=114444\cdot4376874610839020,\qquad
  c(h)=\frac{12W(h)}{1+L_s},\qquad \delta(h)=1-\beta c(h)^2,
  \qquad \beta=204618888056724185.
\]
In particular \(0<\beta c(h)^2<1\) and \(c(h)>0\). Define
\[
 A=1+3\beta(18)^2,\quad
 k=(1-\beta(18)^2)(1-9\beta(18)^2),\quad
 n=\beta k,\quad P=(u,v)=(\beta A^2,\,8\beta^2(18)A(1-3\beta(18)^2)).
\]
Set \(a=v/u\) (the fixed secant coefficient, **not** the original input \(a=0\)) and \(B_0=12n^2/u>0\). The fixed isogenous secant paper gives
\[
  \Delta(m)=((m-a)^2-4\beta A^2)((m+a)^2+B_0).
\]
The remaining **scalar** quantifier at a common index, for this particular first point, is
\[
 \exists h\in\mathscr H:\quad
 \delta(h)\in\mathbb Q^{\times2}
 \quad\text{or}\quad
 \exists m,z\in\mathbb Q,\ z\ne0,\ \Delta(m)=\delta(h) z^2 .
\]
If the complete four-pole theorem is sought using this choice of first point, the other three actual raw PointPairs must in addition be produced at that **same** index. Preparedness is not that assertion. A separately chosen rational \(c\) does not supply the literal \(\delta(h)\). A different \(c\) of the same \(\delta\)-squareclass would also suffice, but would require an additional exact rational square-ratio relation.

## 2. A nonconstant rational family, with finite local compatibility

For any \(q\in\mathbb Q^\times\), put
\[
  w=\frac{q+B_0/q}{2},\qquad
  m=\frac{q-B_0/q}{2}-a .
\]
The parameter \(q\) in these equations is a free rational number, **not** the actual Gaussian denominator prime. Then \(w^2=(m+a)^2+B_0\). If \(m\ne a\), set
\[
 c=\frac{2A}{m-a}=\frac{4Aq}{q^2-4a q-B_0},
 \qquad z=(m-a)w.
\]
These are rational and satisfy \(\Delta(m)=(1-\beta c^2)z^2\), with \(z\ne0\): in fact \(w\ne0\) because \(B_0>0\). Large enough positive real \(q\) gives the required positive \(c\) and \(0<\beta c^2<1\). This is a nonconstant degree-two map in \(c\); the numerator and monic denominator are coprime since \(B_0>0\). It is not just a curve of square complements: the only finite critical points of \(c(q)\) satisfy \(q^2=-B_0\), and each real value \(c=\pm1/\sqrt\beta\) has two distinct real inverse images (the discriminant of the inverse quadratic is strictly positive). Thus \(1-\beta c(q)^2\) has simple geometric zeros and is not a square in \(\mathbb Q(q)\).

For a given actual \(c=c(h)>0\), exact equality to this specialization image is equivalent to the **additional square test**
\[
               \boxed{\ (2ac+2A)^2+B_0c^2\in\mathbb Q^{\times2}\ }. \tag{*}
\]
Indeed the image forces \(m=a+2A/c\). Conversely a rational square root of (*) divided by \(c\) gives \(w\), and \(q=w+m+a\ne0\) since \((w-m-a)(w+m+a)=B_0\ne0\); this recovers the display. Test (*) is sufficient for the complete secant equation at this \(h\), but need not be necessary: the complete secant equation does not prescribe \(m\) or require its second factor to be square. The alternative \(m=a-2A/c\) gives the same statements with \(+2A\) replaced by \(-2A\).

At all already-controlled **scalar** places this extra conic condition causes no new local obstruction:
- At 2, the source gives \(v_2(c)=2\). Also \(v_2(a)=4\), \(v_2(A)=0\), \(v_2(B_0)=2\). The centre \(2ac\pm2A\) has depth 1 and the correction \(B_0c^2\) divided by its square has depth 4. The quotient is \(1\) modulo \(8\).
- At 3, \(v_3(c)=1\), \(v_3(a)=2\), \(A\) is a unit and \(v_3(B_0)=1\). The centre is a unit and the correction has depth 3.
- At every prime \(p\mid\beta\) (including 17), \(c\) is a unit: \(c=12W(h)/(1+L_s)\), and \(W(h)\) is prepared as a unit. Here \(A\equiv1\), \(a\equiv0\), and \(v_p(B_0)=1\), since \(k\equiv1\) and \(\beta\) is squarefree. The centre is a unit and the correction has positive depth.
- At the real place the expression is positive for \(c\ne0\).

In each case the square root gives a genuine \(q\) in that completion by the inverse above, with no zero parameter or pole. Thus ordinary weak approximation in the **rational parameter** \(q\) can make a specialized \(c(q)\) satisfy any finite neighborhoods of those prepared \(c(h)\) at this list of places and at infinity. This says nothing about a different prime from that list, and gives **approximation, not equality** to any \(c(h)\). The actual Gaussian prime theorem produces indices satisfying selected finite congruences and real inequalities; the existing conclusion does not require either (*) or the exact square-ratio relation, and does not furnish a match.

## 3. Why there is no odd-degree rational specialization in the general receiver

Let \(C\) be now an indeterminate, \(K_0=\mathbb Q(C)\), and \(X/K_0\) be the smooth genus-one curve with affine equation
\[
                \Delta(m)=(1-\beta C^2)z^2.
\]
It has no \(K_0\)-point, including projective boundary. To see this, put \(D^2=1-\beta C^2\). The field \(K_0(D)\) is the function field of the nonsingular rational conic \(D^2+\beta C^2=1\), with rational point \((0,1)\). Over it, \(X\) untwists via \(y=Dz\) to the constant curve \(Y:y^2=\Delta(m)\). Any point of this constant smooth proper genus-one curve over the rational function field of the conic is constant over \(\mathbb Q\): it gives a map from a smooth projective genus-zero curve to \(Y\), which extends everywhere by properness and must be constant by Riemann--Hurwitz. The constants of the conic are \(\mathbb Q\). The descent action is \((m,y)\mapsto(m,-y)\), so a descended constant point would need to be a rational fixed point of that involution. Its only fixed points are the roots of \(\Delta\); the two points at infinity are exchanged because the quartic is monic of degree four. The first quadratic factor has roots \(a\pm2A\sqrt\beta\) and the second has negative discriminant. Neither has a rational root.

On the other hand \(X\) **does** have a point over this quadratic extension, by either of the rational constant infinity points of \(Y\). Hence its nonzero Jacobian torsor class has exact order two by restriction--corestriction. For any nonconstant \(C=C(q)\in\mathbb Q(q)\), the function-field degree \([\mathbb Q(q):\mathbb Q(C(q))]\) is the degree of the rational function. If the pulled-back curve has a rational section and that degree is odd, restriction--corestriction makes the nonzero order-two class vanish, a contradiction. This also rules out a projective section. The degree-two family above attains the first allowed degree. This is an obstruction to a generic/rational-base output of odd degree, not an obstruction to a rational point at a given physical \(h\).

## Exact bindings and verification

The common scalar/relative class is pinned by list SHA-256 173d6f342c7a87f71430fe6cb7b2799cc02da878f771095c55cef238d6f3c158, the secant constants and equivalence by e3c9390760080729456a6926e61552a7883aa939ca84ac8156e31a2846782d37, and the sharp-depth scalar and simultaneous four-Ready handoff by 9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5. The small independent arithmetic replay checks the fixed constants, controlled local depth rows, and the displayed family on two exact rational inputs; no actual source \(h\) is used or tested.

~~~sh
sha256sum -c SHA256SUMS
python3 -B replay_degree_two_specialization.py | cmp - EXACT-DEGREE-TWO-SPECIALIZATION.json
~~~
