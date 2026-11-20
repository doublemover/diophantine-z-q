# An exact next cover of the alternate fixed-scalar curve

Keep the actual scalar parameters of 98e26096: \(0<D=\beta c^2<1/9\),
\(\delta=1-D\), \(\beta=204618888056724185\), and write \(c=C/Z\)
in lowest terms with \(C,Z>0\). Let
\[
  H=Z^2-\beta C^2,\qquad L'=49\beta C^2-48Z^2<0.
\]
Here \(L'\) is the alternate Jacobian's discriminant factor,
not the original cut's \(25\beta C^2-9Z^2\).
The existing fixed-rate scalar calculation gives
\(c\equiv76\pmod{256}\) in \(\mathbb Z_2\);
the exact denominator reduction gives \(Z\equiv1\pmod8\);
\(c\) is integral at every prime of \(\beta\), is integral
and divisible by 3 at 3, and is a unit at 7.
The normalized denominator residues are not replaced by residues
of the unreduced expression for \(c\).

This note gives an exact higher cover and primewise necessary
condition on a rational point of the alternate curve; it does
not exhibit one or exclude them all. In particular the product
of the new primewise conditions gives no global obstruction.

## Pairing the two original conic parametrizations

Use the standard full parametrization of
\(U^2+3\beta X^2=4Y^2\):
\[
 P(r,s)=(4rs,\ \beta r^2+3s^2,\ 2(3s^2-\beta r^2)).
\]
The second conic of the alternate curve is the same conic with
\((X,Y)\) replaced by \((X+cY,Y+\beta cX)\) and \(U\) by \(V\).
For a nonzero rational squareclass representative \(\tau\), set
\(D_\tau\subset\mathbb P^3_{r,s,u,v}\) to be
\[
 \begin{aligned}
  4Zrs+C(\beta r^2+3s^2)&=\tau\,4uv,\\
  4\beta Crs+Z(\beta r^2+3s^2)&=\tau(\beta u^2+3v^2).
 \end{aligned}
\]
The projection to the exact alternate curve is
\[
 [X:Y:U:V]=[ZP_X(r,s):ZP_Y(r,s):ZP_U(r,s):\tau P_U(u,v)].
\]
This is everywhere defined: \(P_X,P_Y\) never simultaneously
vanish on \(\mathbb P^1\), and the original two equations
preclude either pair being \((0,0)\) at a projective point.
On a point of the target over an algebraically closed field
of characteristic zero, each conic fixes its own projective
parameter pair. The two equations then determine the relative
square of the two pair scales. This proves surjectivity and
degree two, with the two points in a fiber differing by one
pair's sign, not by a sign of an original ordinate.

For completeness the determinant of the block diagonal pencil,
up to the nonzero constant \(\tau^2\), is
\[
 [3\beta(C\lambda+Z\mu)^2-4(Z\lambda+\beta C\mu)^2]
 [3\beta\mu^2-4\lambda^2].
\]
The blocks individually have two distinct projective roots,
by invertibility of the matrix of determinant \(H\). Substituting
\((\lambda/\mu)^2=3\beta/4\) into the first block gives
\(-7\beta^2 C^2/4-2\beta CZ(\lambda/\mu)\).
Hence no common roots because \(C\ne0\) and \(L'\ne0\).
The cover is smooth: at a singular point of an intersection
a pencil member annihilates the coordinate vector; its simple
determinant root gives one-dimensional kernel, and the
determinant derivative in the other pencil direction is a nonzero
multiple of that vector's second quadratic value, which is zero
on the intersection, a contradiction. Thus \(D_\tau\) is a smooth
genus-one curve and the degree-two projection is geometrically
unramified by Riemann–Hurwitz. No assertion of a full [4] or [8]
multiplication covering is needed.

Every rational point on the alternate curve gives a rational
point on some \(D_\tau\): choose rational parameter pairs of
the two conic triples, and \(\tau\) is the unique proportionality
between their projected pairs after the integer \(C,Z\) matrix.
If parameters are taken primitive at a place \(p\nmid 6\beta\),
both projected pairs have a unit coordinate. For \(p\nmid H\)
the matrix is invertible, so their proportionality is a unit.
Local changes of pair scale multiply \(\tau\) by squares.
This proves \(\tau\) is supported on \(2\cdot3\cdot\beta\cdot H\),
with no new prime from the alternate \(L'\), from \(C\), or
from \(Z\) (outside this same listed support).

Changing the sign of either original ordinate is effected by
\((r,s)\mapsto(3s,\beta r)\) or \((u,v)\mapsto(3v,\beta u)\);
it multiplies the corresponding projected pair by \(3\beta\)
and reverses the ordinate after projective rescaling. In particular
it multiplies the class of \(\tau\) by \(3\beta\).
Writing the second transformed pair over the fractional \(c\)
instead of over \(C,Z\), the tangent ratio computes the class
\[
  \frac{\tau}{Z}\ \sim\
  \frac{2(Y+\beta cX)-V}{2Y-U}.
\]
This follows by \(2P_Y-P_U=4\beta r^2\) (or \(4\beta u^2\)).
For the actual rational chart both tangents are nonzero, as
\(x=0,y=0\) were already excluded at 13. At local boundary
points one can use the other tangent sign before dividing;
the squareclass change is exactly \(3\beta\), as above.

## Actual small-place constraints

* Over \(\mathbb R\), both conic \(Y\)-coordinates in the real
  parametrizations are positive. Indeed \(Y>0\) for the first,
  and \(|\beta c X/Y|\le2\sqrt{D/3}<1\). Thus \(\tau>0\).
* At \(p=3\) or \(p\mid\beta\), a point forces \(x=X/Y\) integral:
  at a negative valuation the first squared ordinate has odd
  valuation (the coefficient \(3\beta\) has valuation 1).
  With \(Y=1\), the second transformed \(Y\) is a unit and
  \(U^2,V^2\equiv4\pmod p\), since \(\beta c\equiv0\pmod p\)
  in these cases. Choose the two ordinate signs to make the
  two tangent terms both \(4\bmod p\). Thus
  \(\tau/Z\in\{1,3\beta\}\) in the local squareclass group.
  Globally reversing just one ordinate if needed makes
  \(v_3(\tau)=0\) in a squarefree representative, since
  \(v_3(3\beta)=1\) and \(Z\) is a 3-unit. In this normalization
  \((\tau/3)=(Z/3)\). This does not lose the rational-point
  implication because the sign-reversed point is also actual.
* At 2, \(v_2(c)=2,\ \beta\equiv1\pmod8\).
  From \(4-3\beta x^2\) being square, either \(x\) is a unit or
  \(v_2(x)\ge3\): at a pole the leading unit is 5 mod 8;
  at valuation 1 the unit test after extracting 4 gives
  a number 6 mod 8; at valuation 2 the unit is 5 mod 8.
  If \(v_2(x)\ge3\), then the second conic argument
  \(y=(x+c)/(1+\beta cx)\) has valuation 2, contradiction.
  Hence with \(Y=1\) the original \(U,V\) are both odd. Their
  squares differ by 8 modulo 16, because \(D\equiv0\pmod {16}\)
  and the linear term in \(q_2-q_1\) is \(2\beta c x\).
  One of \(U,V\) therefore has class \(\pm1\bmod8\), the
  other \(\pm3\bmod8\). The tangent ratio is
  \((2-V)/(2-U)\bmod8\) and belongs to \(\{5,7\}\).
  Since \(Z\equiv1\pmod8\), this forces \(\tau\equiv5\) or
  \(7\pmod8\) and \(v_2(\tau)=0\). The sign change by \(3\beta\)
  preserves this pair of dyadic classes.

In particular any rational point gives a normalized positive
squarefree \(\tau=B_*H_*\), with \(B_*\mid\beta\) and
\(H_*\mid\operatorname{rad}(H)\). Here \(H\) is coprime to
\(2\cdot3\cdot\beta\) by the stated local data.
The classes \(1,3\beta\) alone cannot work.

## Exact shared-line test at every odd-depth prime of the new discriminant

Let \(p\mid L'\), \(p\nmid 2\cdot3\cdot7\cdot\beta\), and
suppose \(v_p(L')\) is odd. Then \(C,Z,H\) are units at \(p\).
In \(\mathbb Q_p\) choose \(\rho^2=3\beta\) with
\(7\rho c\equiv12\bmod p\) and put \(\epsilon=7\rho c-12\).
Such a root lifts since \(3(49D-48)\equiv0\) and \(24\) is
a unit. The conjugate factor \(7\rho c+12\) is a unit, so
\(v_p(\epsilon)=v_p(L')\).
Write \(X_2=X+cY,\ Y_2=Y+\beta cX\). The literal identity is
\[
 7(2Y_2-\rho X_2)=(2Y+\rho X)
   +\epsilon[-Y+(2\rho/3)X].
\]
On the conic parametrizations,
\(2P_Y\mathbin{\pm}\rho P_X
 =2\beta(r\mathbin{\pm}(\rho/\beta)s)^2\).
In local primitive pairs use the unit proportionality
\(\lambda\) from \(X_2,Y_2\) to the second pair; its class
is \(\tau/Z\), with the first pair's common scale fixed to 1.
The identity becomes
\[
  7\lambda(u-(\rho/\beta)v)^2
    -(r+(\rho/\beta)s)^2
    =\frac{\epsilon}{2\beta}[-Y+(2\rho/3)X].
\]
If \(7\lambda\) is a nonsquare unit, reduction forces both
linear forms on the left to vanish. Then \(2Y+\rho X=0\bmod p\),
and the primitive pair \((X,Y)\) has \(Y\) a unit.
The bracket is \(-7Y/3\bmod p\), a unit. The right side
therefore has odd valuation. But the left side, as a difference
of squares with nonsquare unit coefficient, has even valuation
whenever nonzero, a contradiction. We conclude the necessary
condition
\[
            (7\,\tau Z/p)=+1.
\]
For a unit class, this is also sufficient at such a place.
The previous all-place proof supplies a smooth affine residue
point with both squared ordinates nonzero, hence not the shared
branch. Its lift has exactly the required unit class by the
shared-line identity (the first tangent is a unit there).
Rescaling one pair by a local square root of the appropriate
proportionality ratio gives a point on the particular cover.

The prime 83 is an actual odd-depth prime from the exact earlier
prime-square replay: \(\epsilon\equiv5146=62\cdot83\bmod83^2\)
for \(\rho\equiv4470\bmod83^2\).
In that example the reduced common branch is at \(x=14\bmod83\).
The sibling finite check also confirms that all other actual
pairs of residue ordinates have the indicated class (and that
there is no point at \(x=\infty\) in the residue field).
This condition alone does not evaluate \(Z\bmod83\).

## Why the aggregate of all new tests does not suffice

Let \(L_o=-L'/96\). This is a positive odd integer prime to
\(3,7,\beta,Z,H\): the valuations at 2 and 3 are exactly
5 and 1 respectively; the other assertions follow from
\(L'\equiv49\beta C^2\bmod Z\), the actual 7-unit, and
\(L'\equiv Z^2\bmod H\), with \(C,Z\) primitive.
The exact dyadic \(c\) gives \(L_o\equiv3\bmod8\), by
\(\beta\equiv9\bmod16,\ c/4\equiv19\bmod64,\ Z\equiv1\bmod8\).
Multiplying the necessary conditions gives \((7\tau Z/L_o)=1\).
Pure Jacobi reciprocity gives
\[
 (7/L_o)=-1,\quad (Z/L_o)=(3\beta/Z),\quad
 (B_*/L_o)=(-2/B_*),\quad (H_*/L_o)=(6/H_*).
\]
For verification use \(L_o\equiv Z^2/2\bmod7\) and at every
odd prime of \(\beta\); at every prime of \(H_*\) use
\(L_o\equiv-Z^2/96\); modulo \(Z\) use
\(L_o\equiv-49\beta C^2/96\). All these reductions use
only unit denominators at the relevant place.

At every \(p\mid\beta\) the local condition
\(\tau Z\in\{1,3\beta\}\) gives the corresponding unit
character 1 when \(p\nmid B_*\), and the character of
\(3\beta/p\) after stripping \(p\) when \(p\mid B_*\).
Multiplying and canceling the within-\(B_*\) pairs gives
\[
 (Z/\beta)(H_*/\beta)=(3/B_*)(B_*/(\beta/B_*))((\beta/B_*)/B_*).
\]
Here \((H_*/\beta)=1\) by reciprocity since \(\beta\equiv1\bmod4\)
and \(\beta\) is a square at primes of \(H\).
The two cross factors give \((-1/B_*)\), hence
\((\beta/Z)=(-3/B_*)\).
The product of new primewise tests is therefore
\[
          -(3/Z)(6/\tau)=1.
\]
But \(\tau\equiv5,7\bmod8\) implies
\((6/\tau)=-(\tau/3)\), while the same retained 3-normalization
gives \((\tau/3)=(Z/3)=(3/Z)\).
So the aggregate is automatically \(+1\), not an obstruction.
An individual comparison at 83 or another odd-depth prime can
still be nonredundant; such a comparison requires finer support
or unit data than this scalar's aggregate normalizer presently gives.
