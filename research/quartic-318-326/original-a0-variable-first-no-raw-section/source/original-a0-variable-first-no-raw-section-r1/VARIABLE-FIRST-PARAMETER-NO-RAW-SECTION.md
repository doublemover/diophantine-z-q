# No raw companion section over the complete first rational conic at the fixed original scalar

Fix the literal archived \(a=0\) scalar with \(h=473592745039516333133760\),
\(i=6^{15}3^{65536}J\), and the same frozen \(J\). Put
\(B=17b=\beta(17c)^2>0,\ \beta=204618888056724185,\ 
\delta=1-b/17=1-\beta c^2>0\). The pin and bounded source reduction in the
[fixed scalar norm-line replay](../original-a0-factorless-companion-norm-line-r1/ACTUAL-A0-FACTORLESS-COMPANION-NORM-LINE.md)
give \(v_{181}(c)=-1,\ 181c\equiv112,\ \beta\equiv40\bmod181\).
Thus \(v_{181}(\delta)=-2\) and \(181^2\delta\equiv-40\cdot112^2\bmod181\),
a nonsquare (Euler symbol of \(-40\) is \(-1\)). In particular \(\delta\)
is nonsquare in \(\mathbb Q\) without identifying its full squarefree support.
The positive squarefree class \(\beta\) is nonsquare, also by this same
local residue. The argument below keeps both \(B\) and \(\delta\) fixed
while the first rational conic parameter is genuinely variable.

## Exact fibration on the original PointPair

For the two literal cubic equations with the same \(T\) and \(s\ne0\)
let \(z=T/B,\ z'=\delta z/(s/B)^2\). Dividing each ordinate by its
corresponding nonzero factor \(\beta(17c)^3\) and
\(\beta(17c)^3s^3\), respectively, gives the same conic
\[
                        y^2=\beta(1-z)(1+3z).
\]
Its complete rational parameter line is \(\mathbf P^1_t\) with
\(z=(t^2-\beta)/(t^2+3\beta)\), namely the line \(y=t(z-1)\)
through \((1,0)\); \(t=\infty\) covers that basepoint.
Applying the same parametrization with \(t'\) on the companion,
put \(f_\beta(t)=(t^2-\beta)(t^2+3\beta)\). Over \(F=\mathbb Q(t)\)
the remaining **raw** requirement is a point of
\[
                    {\cal D}:\quad W^2=\delta f_\beta(t)f_\beta(t').
\]
Here the projective completion includes \(t'=\infty\) (use the homogeneous quartic, with its leading coefficient \(1\)).
The identity is obtained from \((s/B)^2=\delta z/z'\); conversely
the same square relation gives the original \(s,T\) and two
ordinates, on the nonzero locus of the denominators.
No stronger ordered Kummer class is assumed on the first or second conic.

## The entire generic fibre has no rational point

Take the smooth projective genus-one curves
\[
             C_1:\ u^2=f_\beta(t),\qquad
             C_\delta:\ v^2=\delta f_\beta(t'),
\]
with their respective involutions reversing \(u,v\).
After adjoining \(u\), a hypothetical \(F\)-point on \({\cal D}\)
gives a rational map \(C_1\dashrightarrow C_\delta\) by
\(v=W/u\); it extends to a morphism by smoothness and properness
and is equivariant for the two involutions. This works at
\(t'=\infty\) using ordinate \(v/(t')^2\).

The exact birational map from \(C_1\) to its Jacobian, with the
positive branch at infinity chosen as origin, is
\[
 X=2(u+t^2+\beta),\qquad Y=2Xt,\qquad
 E'_\beta:\ Y^2=X(X^2-4\beta X+16\beta^2).
\]
It follows by multiplying \(u\pm(t^2+\beta)\), whose product is
\(-4\beta^2\) in the order \( (u-(t^2+\beta))(u+(t^2+\beta)) \).
Its invariants give \(j=2048/3\), hence it has no geometric complex
multiplication (CM \(j\)-invariants are algebraic integers).
Inversion of \(u\) acts by \(P\mapsto T_0-P\), \(T_0=(0,0)\):
this follows from \((X,Y)\mapsto
(16\beta^2/X,16\beta^2Y/X^2)\).
On its Jacobian the translation drops out and the induced action
is \([-1]\). Therefore \(J(C_\delta)\) is the quadratic
\(\delta\)-twist of \(E'_\beta\), irrespective of whether
\(C_\delta\) has an origin over \(\mathbb Q\).

The rational Hom group \( \operatorname{Hom}_{\mathbb Q}
(E'_\beta,J(C_\delta))\) vanishes: geometrically it is
\(\mathbb Z\) since the elliptic curves are twists of a non-CM
curve; any Galois element negating \(\sqrt\delta\) negates a chosen
generator. A nonconstant morphism between two smooth proper
genus-one curves would induce a nonzero Jacobian morphism.
The hypothetical equivariant morphism must therefore be
constant. Its value must be rational because \(C_1\) is
geometrically integral. Equivariance requires that constant
to be fixed by reversing \(v\). The complete fixed-point list is
the four branch roots \(t'=\pm\sqrt\beta,\pm\sqrt{-3\beta}\)
with \(v=0\); at infinity the two geometric points with normalized
ordinate \(\pm\sqrt\delta\) are exchanged. None of the four
fixed points is rational. Thus \({\cal D}(\mathbb Q(t))\) is empty.

This is the whole raw first-parameter line, not only the previous
single \(z=1/100\) chart or the smaller first full-mark chart.
It does **not** rule out any rational \(t,t'\) at this fixed
numerical scalar. It also does not rule out a rational base
change for which \(u^2=f_\beta(t(z))\) acquires a new Jacobian
factor. If that double cover stays geometrically integral of
genus one, its nonconstant map to \(C_1\) gives an isogeny of
Jacobians, so it cannot yield a section by the same argument.
A hypothetical section through a rational base change must
therefore meet the genuinely different higher-genus case
(or no longer be a nonconstant base change).

The exact old raw back-map and isogenous model are in the
[archived PointPair Kummer paper](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/actual-original-pointpair-kummer-fibre/ct-original-scalar-kummer-fiber-r1/ACTUAL-RAW-POINTPAIR-KUMMER-AND-SCALAR-FIBER.md).
The separate [first-full-mark paper](https://github.com/doublemover/diophantine-z-q/blob/f767adfb8eba61b98fc865e82f73776f4f095799/research/quartic-318-326/actual-constant15-marked-receiver/rc-native-helper-20261120/ct-original-first-mark-weak-approximation-r1/FIRST-MARK-WEAK-APPROXIMATION-AND-COMPANION-BOUNDARY.md)
deals with the generic elliptic group of that smaller chart.
