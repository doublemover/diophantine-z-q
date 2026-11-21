# A changed norm line for two exact original marks

Fix one original Ready pole b, its positive squarefree classes
β=[17b]>1 and θ=[1−b/17]>1, and an old selected local seed n_*,
n_*θ with the everywhere-local full mark (β,1) in ordered coordinates
(x+3d,x−d) on both curves. In particular n_*>0, n_*≡11 (mod 12),
gcd(n_*,6θ)=1, and θ is locally square at 2,3,17 and at primes
dividing β, while β is locally square at primes dividing θ.
The original pole supplies the exact norm relation
1−β c₀²=θ e₀² with c₀,e₀ rational nonzero.

Here c,e on this same rational conic are **auxiliary**; neither the
original pole nor its input source index is changed. We construct one
rational line Möbius relation between two first-mark parameters for
which the exact companion condition is an everywhere locally soluble
binary quartic. Its rational solubility remains unresolved. No Selmer-
eight, rank, or rational PointPair is inferred from local solubility.

## 1. Exact marked back-map, without independently changing either twist

Write G(t)=1−βt², H(t)=1−9βt² and D(t)=βG(t)H(t).
The first-mark parameter identity in the predecessor gives a rational
point on E_D whose x, x−D, x+3D are β times a square, a square,
β times a square respectively, and parametrizes every local full-
mark nonexceptional twist squareclass. Put

    t' = (t+c)/(1+βct),        1−βc² = θ e².

Then G(t') (1+βct)² = (1−βc²)G(t). The remaining condition is exactly

    W² = H(t) [(1+βct)²−9β(t+c)²].                      (1)

Off the zero factors and poles this says H(t')/H(t) is a square, so
D(t')/D(t)=θ times a square. When D(t)>0, the exact first and second
marked points therefore scale onto E_n,E_{nθ}, with n the positive
squarefree representative of D(t). The square scaling on the second
curve divides both coordinates by the appropriate positive square
and signed cube; the x-squareclass is unchanged. The rational
point on (1) must lie on this specific open, and for the old local
conditions it must also lie in the corresponding address balls.

## 2. One global auxiliary c with all local quartic points

At each protected completion pick finite local t and t' with both
H values in the same squareclass, [D(t)]=[n_*] and [D(t')]=[θ n_*].
We may work off all the finite exceptional points by perturbation.
At a θ-square place take t'=t and choose t in the open chart
of the old full mark; at infinity take t small and nonzero.
If θ is nonsquare and β square, choose both parameters near the same
simple local root of G. The nonzero H there has a fixed squareclass;
the inverse function theorem at that root lets G attain each of the
two required nonzero squareclasses arbitrarily near the root.

If both classes are nonsquare, the mutual local conditions and the
conditions at 2,3 leave an odd prime at which they are both
nonsquare *units*. Also n_* is a unit: the full mark on a
ramified E_{n_*} at an odd p∤β would force the β unit to be square
(the torsion valuations biject on the local 2-Kummer image).
For the pairs ([G],[H]) the chart gives (+,+) near zero and
(ε,ε) near a pole, where ε=[−β] and + denotes the square class.
There is a mixed pair of unit classes: on the opposite unit twist
class from β the curve has good reduction and full rational 2-torsion,
so the full unramified marked Kummer pair is realized, can be made
nonexceptional, and lands in the chart. Moreover G,H cannot have
nonzero valuation on this chart with t integral when β is a nonsquare
unit (both polynomials have no residue root), and for a t pole the
classes agree. If the mixed pair has second entry +, match it with
(+,+). If the second entry is − and ε=−, match it with (−,−).
Otherwise the reciprocal t ↦ 1/(3βt) exchanges G,H and multiplies
each class by ε=+, reducing to the first case. These pairs realize
both prescribed unit twist classes; label t and t' in the desired
order. All these comparisons are open.

For each such pair solve c=(t'−t)/(1−βtt') after perturbing to keep
the denominator nonzero; the displayed G identity ensures
1−βc² has local class θ, so a local e exists. In the θ-square case
c=0 initially works. At the real place choose the old positive chart.
The rational conic of (c,e) has the original rational point
(c₀,e₀) and is isomorphic, projectively, to a rational projective
line. Ordinary weak approximation chooses one global (c,e) near
all the local choices for 2,3,5,∞, the supports of β,θ,n_* and any
further specified finite set. Avoid c=0 and e=0. The original
local marked conditions for both parameters and (1) remain open:
for each protected place the chosen t can be retained while c varies
slightly, using openness of the nonzero square on the right of (1).

For any unprotected prime p≥7, β is a unit. If c is a nonunit
integer locally, take t near zero (the right side is a unit square).
If c has a pole, divide the right side by c²; its reduction is
H(t)(β²t²−9β), a separable binary quartic (root overlap would force
p=2 or 5). Its genus-one good reduction has an F_p-point by Hasse;
smooth lifting and perturbation avoid all the exceptional points.
If c is a unit and βc²≡1, take t≡c: the two factors are −8 and −32,
with square product 256. Otherwise both binary quadratics have
simple roots, and a common root can occur only when 25βc²≡9, by
substituting t=±1/(3√β). For p≥7 in that case exactly one root is
shared, and it is rational over F_p. The quartic is L² times a
separable binary quadratic after reduction. The normalization is
a smooth conic over F_p with p+1 points; at most two lie over the
shared root. A smooth point off that root lifts, then can be perturbed.
In all other cases Hasse and smooth lifting again apply. These are
binary statements, including factors whose root is infinity.
This proves all-place admission on the exact open, not the Hasse
principle for the rational genus-one curve.

## 3. Exact Jacobian, marked torsor, and one remaining rational x-class

Let μ=βc² and δ=1−μ. In v=t/c the equation is

    W² = (1−9μv²)[(1+μv)²−9μ(v+1)²].

Its elliptic Jacobian and T₀=(0,0) quotient are

    J :  Y² = X(X−16μ²)(X−μ(25μ−9)),
    J':  Y² = X[X²+2(41μ²−9μ)X+(9μδ)²].

Here is an exact check including the twist and class. Set k²=μ and
z=3kv. The first factor is 1−z²; write F(z) for the quartic. Its
other roots are z₊=3(1−3k)/(3−k) and z₋=−3(1+3k)/(3+k), and
F'(1)=32k(3+5k)/9. The rational branch-root coordinates over Q(k),

    X₀=F'(1)[1/(z−1)+1/2],   Y₀=F'(1)W/(z−1)²,

give a monic split cubic with roots 0, 4(25μ−9)/9, 64μ/9.
Scale X₀,Y₀ by (3k/2)²,(3k/2)³ to obtain J. The resulting differential
dX/Y=−2dv/W is rational. The conjugate isomorphism thus has the same
linear part (the differential distinguishes origin-preserving
automorphisms in characteristic zero), and sends the old origin
branch to T₀ because conjugation swaps z=±1. The exact descent
cocycle is χ_β T₀. All three roots are distinct: nonzero rational c
with nonsquare β gives μ≠1,9/25.

By the ordinary [2]-isogeny Kummer sequence for J→J' with kernel
T₀, the image of β in H¹(Q,J) is this genus-one torsor, and it
vanishes iff β is a rational scalar x-Kummer class on J'. The
same statement holds locally, so §2 proves local membership,
not global rational membership. In fact the explicit
P₄=(9μδ,8μ·9μδ) on J' has double (0,0), and its rational x-class
is βθ. (Use the tangent formula or the identity X(P₄)²=(9μδ)².)
Consequently the local/global β test is equivalently the θ test
on this same J'. It is not deduced from the product βθ.
Even a certificate of vanishing still has to yield a rational
point of (1) on the particular positive open, with the specified
old rows if those are required. No weak approximation for elliptic
rational points is used.

## 4. Positive exact arithmetic control, not an original pole

The earlier independent two-point arithmetic control has β=17,
θ=1033 and twists 323 and 333659. Its known b is globally square;
this replay does not identify any admissible linked source index.
The full-mark parameters t=75/1139 and t'=27/391 give the *changed*
norm-line c=21/6043, with δ=1033(188/6043)² and nonzero W in (1):

    W=139679488/461159459,
    D(t)/323=(9776/76313)², D(t')/333659=(32/8993)².

Both H have class 646. The exact replay checks both points, their
three coordinates, Jacobian invariants in the chosen normalization
(c₄=I, 2c₆=J for the displayed quartic's classical binary invariants),
and the genuine target order-four point.

    python3 -B replay_changed_line.py | cmp - EXACT-STRONG-MARK-RECEIVER-CONTROL.json
    sha256sum -c SHA256SUMS
