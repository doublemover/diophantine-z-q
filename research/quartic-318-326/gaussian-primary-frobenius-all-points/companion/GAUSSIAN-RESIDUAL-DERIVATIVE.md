# The selected Gaussian scalar on the actual residual curve

Let k be a field of characteristic different from 2, let i in k satisfy
i²=−1, and use the fixed elliptic curve

    E: Y²=X³−X,  O at infinity,  J(X,Y)=(−X,iY).

For a,b in ℤ write G=[a]+[b]J as an endomorphism of this very curve.
Suppose that a+b·i=0 in k. Suppose that the image of the actual generic
point is finite and that its abscissa, in k(E), is A(X)/B(X) with
A,B in k[X] and B≠0. Then

    A′B−AB′=0 in k[X].                                      (1)

No characteristic-zero degree, prime distribution, or bound on the poles
is used in (1). When k=F_p for a prime p≥5, assume in addition that A,B
are coprime and deg B<deg A≤p. Then the abscissa is exactly ±X^p.
In fact G on this curve is coordinate p-power Frobenius followed by
one of 1, J, −1, −J. These extra degree hypotheses are explicit here;
the argument does not establish the characteristic-zero degree input
from which the specialization proof obtains the cap.

## 1. Actual formal parameter and stationary scalar

Do the local test over an algebraic closure K of k. The literal ring
K[X,Y]/(Y²−X³+X) is a domain: X³−X has odd degree, so cannot be a square
in K(X), by comparing degrees after clearing denominators. Passing
from k to K therefore gives the natural injections on this ring and
its fraction field. J and G commute with this coefficient extension
by the stock affine formulas and their tangent and inverse branches.

Work over K((t)) with valuation ring K[[t]]. For original kernel points,
write s=−x/y and w=−1/y, with values (0,0) at O. The literal equation is

    w+s w²=s³.

At s=0 the derivative in w is 1, so there is a unique w(t)∈tK[[t]]
with w(t)+t w(t)²=t³, and w(t)=t³ times a unit. This gives an actual
point P(t)=(t/w(t),−1/w(t)), reducing to O, with parameter exactly t.
For any point reducing to O both its formal coordinates are small: if
x has negative order then y has 3/2 its order, and −x/y and −1/y have
strictly positive order. The zero point is a separate allowed branch.

The linear coefficient of s on the kernel is additive. For clarity,
the literal projective origin chart is [−s:1:−w]. If two kernel points
have coordinates (s_j,w_j), the connecting line has w=λs+ν, where the
divided difference formula gives

    λ·(1+s₂(w₁+w₂)) = s₁²+s₁s₂+s₂²−w₁².

This holds also for the tangent at s₁=s₂; at two equal parameters
the corresponding small w is unique. Thus λ∈(t²), ν∈(t³). The cubic
for intersections is

    (1−λ²)s³−2λνs²−(λ+ν²)s−ν=0.

All three projective intersections are in this chart: if Y=0, the
chord relation gives Z=λX and forces (1−λ²)X³=0, impossible. By Vieta
and the negation (s,w)↦(−s,−w), the sum's parameter is

    s₁+s₂−2λν/(1−λ²).

Its last term belongs to (t⁵); inverse and zero branches have the
same linear rule (inverse has s₁+s₂=0, zero is the identity).
The third chart point is small from the formula, and its line relation
then makes w small too. This proves the needed additivity directly
on the original chart, including the tangent. The chosen turn J
multiplies s by i (since i⁻¹=−i). Integer scalar combinations
preserve the kernel and its first-jet coefficient is therefore
multiplied by a+b·i. Hence G(P(t)) reduces to O and its original
parameter belongs to (t²). The assertion allows G(P(t))=O.

## 2. The actual mixed chord supplies two compatible germs

Fix x₀,y₀ in K with y₀²=x₀³−x₀, y₀≠0 and B(x₀)≠0. Let Q=(x₀,y₀).
For a small kernel point with parameter s and auxiliary w, and any
constant finite Q=(x₀,y₀), its translated abscissa is

    x(P_s+Q) = x₀ + s·u·v²·H,
    u=(1+s w)⁻¹,  v=(1−x₀s²u)⁻¹,
    H=2y₀+(3x₀²−1)s−(x₀³+x₀)w.

Both denominators are units in K[[t]]. To verify this is the stock
chord, its slope is −(1+y₀w)/(s−x₀w). Subtract x₀ from the abscissa
slope²−s/w−x₀ and clear w(s−x₀w)²: the numerator is exactly w²H,
using w+s w²=s³ and y₀²=x₀³−x₀. Then substitute w=s³u and
s−x₀w=s/v. A nonzero origin-kernel point has a pole in x, so
this secant is never the generic vertical or tangent branch.
For P_s=O the equality is x(Q)=x₀.

Modulo (s²) in the integral expression, u and v have constant value
1 and H has constant value 2y₀, so

    x(P(t)+Q) = x₀+2y₀t mod (t²).                           (2)

In particular that abscissa is different from its constant term.
Over algebraically closed K, every element algebraic over K in
K((t)) is already constant; equivalently, one can repeatedly divide
a supposed polynomial equation by X−x₀, reducing the degree. Thus
the actual point P(t)+Q gives an injection K(E)→K((t)): on K(X)
the first coordinate is transcendental; the quadratic polynomial
for Y is irreducible since X³−X is not a square in K(X). Under this
injection the finite generic abscissa of G maps to the actual
abscissa A(x(P(t)+Q))/B(x(P(t)+Q)). This uses the commutation of
the stock coordinate group law with that same field injection.

The evaluated quotient is integral, since its denominator has
nonzero residue B(x₀). If G(Q) were O, G(P(t)+Q)=G(P(t)) would
reduce to O and could not have finite integral abscissa, a contradiction.
Thus G(Q) is a constant finite point; write its abscissa as z₀.
Applying the same mixed formula at G(Q) with G(P(t)), whose
parameter is now in (t²), gives

    x(G(P(t)+Q)) = z₀ mod (t²).                              (3)

Both (2) and (3) use the same t, the same Q, and the same G.

## 3. Cross-polynomial and descent to the original field

With ε=t mod t², work in K[ε]/ε². The coefficient of ε is
faithfully read by the K-linear map taking an element's degree-one
coefficient. Cross multiplying the integral quotient in (2)–(3)
gives first its constant equality z₀B(x₀)=A(x₀), then

    2y₀·(A′B−AB′)(x₀)=0.

Our restrictions imply 2y₀≠0. For every x₀ outside the zero set of
B(X)(X³−X) some such y₀ exists over K. Multiplying A′B−AB′ by that
nonzero polynomial gives a polynomial that vanishes at every element
of the infinite field K. It is zero, and cancellation gives (1) over K.
The coefficient injection k→K gives precisely (1) over k. This is
also the prime-field statement, not an asymptotic or a density assertion.

## 4. Optional original prime-ring normalization

Suppose now k=F_p, p≥5, and the additional normalized degree inputs
from the theorem hold. Coprimality and (1) give A∣A′ and B∣B′. The
derivatives are zero since otherwise differentiation decreases degree.
Only exponents divisible by p can occur. Since deg B<deg A≤p, B is
constant and A/B=cX^p+d for c≠0.

The involution fixing X and negating Y commutes with scalar formulas
and is negation on the generic point. Thus the ordinate of G is odd
under the involution and is exactly (U(X)/V(X))Y. To see this without
a division at a branch point, express the ordinate as a quotient of
two affine chart elements and multiply by the conjugate of its chart
denominator: the product denominator is fixed and nonzero. The
numerator is anti-invariant; the free chart basis (1,Y) and 2≠0 give
the indicated form. Reduce the rational ratio so U,V are coprime.
The exact curve equation and F_p coefficient powers now give

    U²(X³−X)=V²(((cX+d)³−(cX+d))^p).                        (4)

At each r∈{0,1,−1}, the factor X−r occurs simply in X³−X. If the
polynomial inside the p-th power on the right did not vanish at r,
(4) would force V(r)=0, and U(r)≠0 by coprimality. The right side
would then be divisible by (X−r)² and the left side would not. Thus
cX+d maps all three distinct elements 0,1,−1 to 0,1,−1, permuting
them. Their sum gives 3d=0, so d=0, c=±1. Finally v²=cY^(2p);
since the field is a domain and i²=−1, v is ±Y^p if c=1 and
±iY^p if c=−1. These are exactly the four stated turns after
coordinate Frobenius on the generic curve. Equality on the actual
curve follows from equality on the dense open with finite defined
coordinates, or for group points by subtracting two good translates.

This step does not choose the primary unit. That requires the
separate exact (1+i)^3 torsion calibration on the same chosen residue
place, not an arbitrary sign or orientation. It also does not replace
the separately supplied finite rational presentation and its degree
cap. No Lean compilation or prime-pattern/rank conclusion is claimed.
