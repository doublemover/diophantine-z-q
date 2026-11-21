# One principal PEL lattice gives both exact KS and Hodge metrics

No point or modular quotient is changed. Work at the literal noncontact
marked point on the same selected polarized D=210 abelian surface.
At each embedding of the common height field use the actual genuine
complex lift to the upper half plane from Yuan §4.2–4.3, with
relative curve direction retained. The characteristic-zero level-33
refinement of the chosen 3/11 levels pulls back the same universal
abelian surface and principal polarization; the connecting map is
the earlier same-family Čech connecting map. The construction below
is for this A, not the independently used modular Jacobian J.

## Recover the metric directly from the actual principal form

Write tau=x+iy and use the split-real quaternion realization as
2-by-2 matrices. Yuan's actual torus is C²/Lambda_tau, with
Lambda_tau = O_B*(tau,1) in this local complex uniformization.
Fix the ordered real coordinates (a,c;b,d) for a matrix
[[a,b],[c,d]], and put the actual ordered O_B lattice columns in T.
No numerical lattice basis or norm bound is assumed. Let nu=mu^(-1);
the actual polarized quaternion square mu^2=-210 fixes
nu=-mu/210 and det(mu)=210. For example (mu^2)_11=-210 makes the
upper right entry nonzero over R; the off-diagonal equation gives
trace zero, and the same (11) equation then gives the signed det.

For two matrices X,Y the literal main involution Y^ι is adj(Y) in
the split real algebra. In the indicated order the form
(-Tr(X adj(Y))) has Gram G of signed cross-pairing with G²=I.
Left multiplication by nu acts by blockdiag(nu,nu).
Thus the actual principal-polarization Gram of
[Section 4.2](https://arxiv.org/html/2205.11334v2#S4.SS2) is

    E_T = (blockdiag(nu,nu) T)^t G T .

Its determinant has absolute value 1 because the polarization is
principal. The determinant gives without any trace-codifferent
input or separate covolume premise

    1 = |det(E_T)| = (det nu)^2 |det T|^2 ,
    hence |det T| = 210.

This proof uses the self-dual principal lattice of the same abelian
surface, not an additional order class/discriminant match or a
replacement principally polarized surface. It supplies the
covolume that [Yuan §4.3](https://arxiv.org/html/2205.11334v2#S4.SS3)
also computes by the trace-dual order index.

Now take real coordinate order (Re z1,Re z2;Im z1,Im z2) on C².
The genuine period map T -> Lambda_tau is multiplication by

    B_tau = [[x I₂,I₂],[y I₂,0]].

Block swapping gives upper triangular blocks I₂,y I₂; the swap
has absolute determinant 1. Thus its actual volume is 210*y².
In this same grouped order (dz1,dz2; dbar z1,dbar z2) has wedge
matrix [[I₂,i I₂],[I₂,-i I₂]], with signed determinant (-2i)²=-4.
This fixes the absolute measure of the differential wedge,
rather than assuming the factor four or interchanging the ordering
of holomorphic forms. With the same normalizing measure (2*pi)^(-2)
from Yuan §4.3, the squared Hodge norm of the actual determinant
frame c(dz1∧dz2) is

    |c|² * 210*y²/pi².

The Lean metric theorem derives this formula from the actual ordered
period lattice and its principal integral form, rather than asking
for a separate archimedean scalar norm row. The equality of this
Lebesgue-lattice expression with the actual Faltings definition uses
the torus uniformization and arbitrary-basis fundamental
parallelepiped, classically; Lean here computes the exact determinants.

## The same connecting row and its two joint signs

On an overlap lifted to H × C², the difference is the deck element
beta and sends z_j to z_j+beta_(j1)*tau+beta_(j2). The first
coefficient, with d(tau), is the Čech connecting representative
(as produced by the prior native connecting operator on this
exact sequence). The analytic H^1 comparison uses the principal
polarization character on the very same lattice
exp(2*pi*i*E(epsilon*z, beta)). Its derivative at the identity is
2*pi*i times the fixed Riemann form; the source verifies this
literal derivative of the character as well as the deck slope.

The signs of the TWO columns can be made independent of scalar
convention at the determinant level. With the displayed pairing
E(X,Y)=-Tr(nu X adj(Y)), the matrices

    beta_1 = mu (-E_22),   beta_2 = mu E_12

represent +beta'_(11), +beta'_(21) respectively. Indeed
-Tr((-E_22) adj(beta'))=+beta'_(11), and
-Tr(E_12 adj(beta'))=+beta'_(21). The two matrices with
the opposite common sign shown in the subsequent display in
Yuan §4.2 give the negatives if that displayed E is used
literally. This is an exact display-orientation check, not a
claim that a different principal polarization is used or that
the paper's bicanonical map has a sign error. Using the signed
representatives above, these have zero first column and second
columns (-b,-d) and (a,c) for mu=[[a,b],[c,d]].
Changing both signs (equivalently the common cocycle orientation)
does not change the determinant: the determinant of the
two-column signed row with the actual 2*pi*i denominator is

    210/(2*pi*i)^2.

The proof of the signed row and both-column sign invariance is
separate from the metric computation. No Faltings normalization
is taken as evidence for a particular signed first-order row.
At the ordinary point t, pull the upper-half-plane coordinate
back along the same holomorphic branch. The actual bicanonical
map acts on the square of its cotangent, so it inserts exactly
the two derivative factors. The existing normalization theorem
now receives the principal-lattice computation in place of an
assumed archimedean Hodge square. It keeps the same literal
sections and all quantitative height offsets.

## Scope and replay

The computations use true uniformization of the same marked PEL
surface over the two levels, the same arithmetic polarization
and its analytic identification with the lattice character, not
representability or cohomology formalization by another name.
The algebraic-to-analytic comparison of the universal PEL family,
Appell–Humbert/Picard identifies the character with the Hodge
cohomology, and the differential wedge integral realizes the stated
Faltings metric classically. No native full Hodge/Picard object,
change of the stable height convention, compiled Lean theorem or
end-to-end proof claim. This is complementary to the separately
proved integral KS comparison on the original closed stalk.

    sha256sum -c SHA256SUMS
    python3 check_principal_period.py | cmp - EXACT-PRINCIPAL-PERIOD.json

The replay uses independent exact row determinants, finite shears of
a principal-form test lattice, varied split realizations of mu, and
the two character signs. Sample lattices are arithmetic controls,
not offered as a new classification or as periods of the selected A.
