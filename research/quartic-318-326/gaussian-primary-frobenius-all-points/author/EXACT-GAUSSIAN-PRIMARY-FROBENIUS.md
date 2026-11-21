# Positive primary Frobenius on the chosen Gaussian residue curve

Let π=a+bi be a primary Gaussian prime of norm p≥5, with the chosen
place (π) of ℚ(i); thus its chosen residue root i₀ in F_p satisfies
a+b·i₀=0. Primary means

    π−1=(1+i)³(c+di),
    a=1−2(c+d),   b=2(c−d)                         (c,d in ℤ).

Take the literal curve E: Y²=X³−X and the quarter turn
J(X,Y)=(−X,iY), or (−X,i₀Y) at the chosen residue root. Write
G=[a]+[b]J. The selected residual G is coordinate p-power on every
point of E over any extension of F_p, with no residual degree theorem
for [p] and no automorphism classification. The classical
characteristic-zero uniformization used below is explicit. This is a
paper proof, not a claim of Lean completion or of any rank or
prime-distribution result.

## 1. Exact degree on the original complex curve

Use the actual embedding ℚ(i)→ℂ taking i to the chosen square root.
On E(ℂ), [Silverman, *The Arithmetic of Elliptic Curves*, VI Corollary
5.1.1](https://www.math.ens.psl.eu/~obenoist/refs/Silverman.pdf#page=190)
gives an analytic group isomorphism ℂ/Λ→E(ℂ) for a full lattice.
An identity-preserving holomorphic group map lifts to an additive
entire map: the defect of additivity of an origin lift takes values
in the discrete lattice and vanishes at the origin. The lift is
therefore multiplication by its derivative. The literal parameter
s=−X/Y satisfies s(JP)=i s(P), so the lift of J is multiplication
by i, not −i. Therefore G lifts to multiplication by a+bi, inducing
a surjection of the torus with exactly [Λ:πΛ]=p points per fibre
(real determinant a²+b²).

The actual generic abscissa of G is even under Y↦−Y, because
G commutes with negation; multiplying the affine-chart denominator
by its reflection as usual puts an even rational function in the
literal fraction field ℚ(i)(X). Write it as its reduced A/B.
Its coefficient embedding to ℂ is the abscissa of the same stock
Gaussian scalar on the complex curve. The two meromorphic functions
agree on the dense affine open where the formulas are read, hence
they agree everywhere as meromorphic functions. In particular a
finite value cannot be the abscissa of O. This function is
nonconstant by surjectivity. For a generic finite target c₀, A−c₀B has degree
D=max(deg A,deg B) and exactly D distinct roots. To choose such a
c₀, exclude the value at infinity, values at finite roots of the
nonzero derivative numerator A′B−AB′, and images of 0,±1, along
with 0,±1 as target values. No root of A−c₀B can be a root of B by
coprimality. Hence each of its D roots is the abscissa of two
complex points and neither is a pole of the scalar abscissa.
Those 2D points are exactly the inverse images of the two points
over c₀; each of the two fibres has p points. Thus D=p on the
same original curve. This proves the needed degree cap and does not
use a degree formula for a residual isogeny.

## 2. The cap belongs to the same reduced generic scalar

The literal good curve and local reduction give a group map at the
chosen place; for example one can use the explicit affine and
origin chord cases for this curve. At the curve's Gauss place its
generic point reduces to the actual generic point over F_p. The
residual G of this point is finite: in the same function field
translation by T₀=(0,0) is (X,Y)↦(−1/X,Y/X²). It fixes the chosen
constant i₀ and hence commutes with the coefficient formulas for G.
The quarter turn fixes T₀, and a+b is odd since a²+b² is odd, so
G(T₀)=T₀. If G of the generic point were O, this same translation
comparison would give 0=T₀, a contradiction.

Thus the original generic abscissa is integral in the localization
of the literal valued chart at the generic prime of its special
fibre. Write it there as C/D with D̅≠0. Scale A and B together so
all coefficients are integral and at least one is a unit. The
literal equality AD=BC in the chart implies A̅D̅=B̅C̅.
If B̅=0, the special chart domain and D̅≠0 imply A̅=0, contradicting
primitivity. Therefore A̅/B̅ is the abscissa of the same actual
residual scalar. Its reduced coprime numerator and denominator
still have degrees at most p.

The residual abscissa has a pole at O. This last point can be checked
without a residual degree theorem: on the actual Laurent origin
arc, X has a pole, and the scalar reduces to O. For a polynomial
A, X^(−deg A)A(X) has its nonzero leading coefficient as residue
(apply the reversed polynomial at 1/X). Hence a reduced A/B of
numerator degree at most its denominator degree would be integral
on that origin arc. Faithful evaluation of the generic formula
on that arc would give an integral abscissa for a finite scalar
image reducing to O, which is impossible.

Apply the separately signed **Gaussian residual derivative** proof
to this normalized residual ratio. Its hypotheses are now supplied:
the actual generic image is finite, its literal coefficients have
a+b i₀=0, and the degrees satisfy deg B<deg A≤p after reduction and
cancellation. Its conclusion gives exactly the four options
G(P_gen)=ε Fr_p(P_gen), ε∈{1,−1,J,−J}, on the actual residual generic
point. It does not yet choose ε.

## 3. Two actual Laurent substitutions choose the primary unit

Use the actual origin arc P(t) over F_p((t)), with s(P(t))=t and
w+t w²=t³. Put Q=(i₀,1−i₀). It lies on E, has nonzero ordinate,
and the stock tangent slope is −(1+i₀). Squaring and using the
reflected ordinate formula gives [2]Q=T₀ exactly. The quarter
turn sends Q to Q(−i₀)=(−i₀,1+i₀), whose double is also T₀ by the
same tangent at the opposite root. Consequently

    G(Q) = Q − (c+d)T₀ + (c−d)T₀ = Q − 2d T₀ = Q.

Evaluate the exact generic identity on the actual two Laurent
points P(t) and P(t)+Q. Both induce field injections from F_p(E).
For P(t), the pole in X prevents any polynomial relation in X:
the highest degree term has uniquely least Laurent order. For
P(t)+Q, the literal mixed chord gives x=i₀+2(1−i₀)t mod t².
A polynomial in that x can be expanded at i₀; its least nonzero
power of x−i₀ has uniquely least Laurent order. In both cases the
second coordinate extends the injection because the original
quadratic equation is irreducible over F_p(X), as X³−X has odd
degree. Those embeddings carry both stock homomorphisms in the
generic equality to the same actual maps on the Laurent group.
Subtract the two comparisons; this gives G(Q)=ε Fr_p(Q).

Coordinate Frobenius fixes Q, whose coordinates are in F_p. The
other three unit candidates do not fix Q: J and −J change i₀ to
−i₀, and −1 changes the nonzero ordinate's sign. Thus ε=1 at the
chosen place. There is no independent choice of a sign at another
prime or torsion row.

## 4. All actual residual points and the arithmetic boundary

If R=(x,y) over any extension k/F_p has y≠0, apply the same two
arc tests over k((t)) at P(t) and P(t)+R. The first abscissa is a
pole and the second has nonzero coefficient 2y, so the tests
remain faithful on the actual function field, after base change.
Subtract and descend along the injective coordinate map k→k((t)).
That proves G(R)=Fr_p(R). At O both maps give O. At affine R of
ordinate zero, pass to k(E) and let T be the actual generic point.
Its ordinate is nonzero and hence its double is not O (the tangent
is finite); 2R=O, so 2(T+R)=2T≠O. Both T and T+R therefore have
nonzero ordinate. Subtract their two already established
comparisons; then descend through k→k(E). This proves all-point
agreement, with no geometric continuation theorem.

To identify a chosen arithmetic Frobenius on original prime-to-p
torsion, still bind the actual valuation place and its arithmetic
residue action, use same-place compatibility of stock scalar
reduction, and use injectivity of reduction on that torsion. The
result here is the positive equality in the residue group supplying
that step. Neither the class-field quotient, a Gaussian prime
distribution theorem, nor a rational point of the target quartic is
asserted by this paper.
