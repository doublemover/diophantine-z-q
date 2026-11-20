# The remaining global class on the exact cut is theta, not rank

Scope: exact arithmetic reduction for the same auxiliary genus-one
cut, not a global supply of points, not replacement of the actual b,
and not an assertion that the attached `E_c` is the original
E_n curve or a preexisting RC input.

Use the exact notation D=βc², δ=1−D=θe², with c>0, and the cut
curve E_c from SCALAR-SAME-THETA-GENUS-ONE-CUT.md. Set

    K = 9βδ, M = 8βc, a = M²−2K.
    E_c : y² = x((x−K)²+M²x).

This is literally the same E_c: K²=b_c and a=β(82D−18).
The point T=(0,0) is nonzero rational 2-torsion. The point

    P = (K, MK)

is rational and nonzero. The tangent slope at P is M because
f′(K)=2M²K and y=MK; since a=M²−2K its doubled x is
M²−a−2K=0 and doubled y=M(K−0)−MK=0. Hence [2]P=T
and P has exact order four. Its x-squareclass is βθ
since K=9βθe², **not** β when θ≠1.

The standard x-class Kummer homomorphism of the rational
2-isogeny is x-class for x≠0, identity at O, and class K²
(again identity) at T. This is the usual connecting map
for the dual isogeny and on a secant follows from the
product-of-three-abscissas identity coming from the square
of the intercept. Adding P therefore bijects the actual
class-β rational points with the actual class-θ points.
Both classes are nonidentity for θ>1, so no O or T occurs.
Thus the global rationality input for the cut is exactly
existence of a rational point of this auxiliary E_c with
x-squareclass θ (equivalently the trivial image of that
specific locally soluble 2-isogeny torsor in its Sha).
Rank positivity, without control of this actual class, is
not enough. When θ=1 the 4-torsion point makes the torsor
rational but does not place its t in selected local open sets;
the equal-twist situation is simpler by reusing a direct
marked quartic point instead.

If c=C/Z in lowest terms, Z>0, write H=Z²−βC²>0. Apply the
square scaling x↦Z²x and y↦Z³y. The literal integer models are

    K_int = 9βH,  M_int = 8βC,
    a_int = β(82βC²−18Z²),
    a_int²−4K_int² = 256β³C²(25βC²−9Z²).

They preserve the same global θ=sf(H) x-class and the same
4-torsion formula. The exact θ-isogeny quartic may be written

    M_int² + θ(r − (9βH/θ)/r)² = v²,  r ≠ 0,

using x=θr² and v=y/x. This follows by dividing the cubic
equation by x², with 9βH/θ an integer (θ|H).
Mutual norm identities from the original b do not solve
this quartic automatically.

The prime support for the x-class descent on E_c is finite:
away from p|K_int every affine x of a rational point
has even valuation. If v_p(x)<0 the cubic x³ dominates;
if v_p(x)>0 and p∤K_int, the K_int²x term dominates.
The x-class therefore lies among positive squarefree divisors
of K_int, with negative sign excluded because
y²=x[(x−K_int)²+M_int²x] and the quadratic is positive for
all real x (its discriminant is negative).
The exact dual-isogeny model has two nonzero roots
(8βC)² and 4β(25βC²−9Z²), sign + and − respectively.
Outside their zero factors its x-class similarly has even
valuation. These finiteness reductions do not determine the
two actual rational squareclass images.

There is a robust local computation that can support
a later exact descent once C,Z are supplied. If p≥5
divides H and 5|β for a=0, then p∤β,C,Z. Modulo p the
cubic of E_c has its double root at 0 with tangent slopes
±M_int, so split reduction and unit coefficients. Its
dual has two nonzero roots colliding at M_int² and the
same split tangent class. The minimal discriminant
valuations are exactly 4v_p(H) and 2v_p(H), respectively:
use Δ=16K_int⁴(a_int²−4K_int²) and the dual quadratic
discriminant 16K_int², and their unit c4. Thus the types
are split I_{4v_p(H)} and I_{2v_p(H)}. This is an exact
local ratio 1/2 for the canonical degree-two isogeny at
these primes, not enough to determine global Sha/the mark.
