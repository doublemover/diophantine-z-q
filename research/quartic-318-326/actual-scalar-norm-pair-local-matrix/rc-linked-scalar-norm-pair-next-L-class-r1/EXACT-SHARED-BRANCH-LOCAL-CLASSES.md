# Exact local classes at every new discriminant prime

This is a separate refinement of the exact alternate next cover
(dfc383d9), retaining the same \(c=C/Z,\ \beta,\ H,\ L'\) and
a fixed squarefree \(\tau\) supported on \(2\cdot3\cdot\beta\cdot H\).
It changes no point or scalar and makes no global solubility claim.

Let \(p\mid L'=49\beta C^2-48Z^2\) with
\(p\nmid2\cdot3\cdot7\cdot\beta\), and put \(e=v_p(L')>0\).
The class \(\tau/Z\) is a unit at \(p\).
For the exact two-quadric next cover \(D_\tau\), the local table is

| Condition on \(p,e\) | Admitted unit classes of \(\tau/Z\) |
|---|---|
| \(p\equiv1\bmod4\) (any \(e\)) | \(1/7\) only |
| \(p\equiv3\bmod4\), \(e\) odd | \(1/7\) only |
| \(p\equiv3\bmod4\), \(e\) even | \(1/7,\ -1/7\) (both) |

Unit classes are in \(\mathbb Q_p^\times/\mathbb Q_p^{\times2}\).
The extra restriction in the first row at even depth is
invisible to a Jacobi product weighted by the depth.
The result does not extract the unseen prime support of \(L'\).

## Nonshared and shared branches have prescribed classes

Choose \(\rho^2=3\beta\) with \(7\rho c\equiv12\bmod p\),
as in dfc383d9; put \(\epsilon=7\rho c-12\).
Then \(v_p(\epsilon)=e\).
On a primitive first conic \((X,Y)=(4rs,\beta r^2+3s^2)\)
with \((r,s)\) primitive and on the likewise primitive
second conic parameter pair \((u,v)\), the two transformed
projected coordinates \((X_2,Y_2)=(X+cY,Y+\beta cX)\)
are obtained by multiplying its projected coordinates by
some unit \(\lambda\) with class \(\tau/Z\). Four line
identities follow from
\(2P_Y\pm\rho P_X=2\beta(r\pm(\rho/\beta)s)^2\).

Away from the shared root \(2Y+\rho X=0\bmod p\), the exact
line comparison
\[
 7(2Y_2-\rho X_2)=(2Y+\rho X)
   +\epsilon[-Y+(2\rho/3)X]
\]
gives class \(\lambda=1/7\) in the unit squareclass group.
The earlier smooth split-square count supplies a residue point
outside all three roots; take \(Y=1\) and lift the two nonzero
square values separately by unit Hensel. This always realizes
the \(1/7\) class on an actual local point of the base curve.

On the shared residue root, \(Y\) is a unit,
\(X\equiv-2Y/\rho\), \(Y_2\equiv-Y/7\), and
\(\rho X_2\equiv2Y_2\). Thus the two *opposite* tangent
lines are units and satisfy
\[
 \frac{2Y_2+\rho X_2}{2Y-\rho X}
 \equiv \frac{4Y_2}{4Y}\equiv-1/7\bmod p.
\]
Their quotient has class \(\lambda\) by the same conic
square identities. This proves the claimed necessary unit
class at every shared-branch lift, even for arbitrarily
large \(e\). At split primes \(p\equiv1\bmod4\) it gives the
same unit class as the nonshared branch. At nonsplit primes
the class is distinct, and the odd-valuation nonsplit norm
test in dfc383d9 rules out the shared branch when \(e\) is odd.

## A true shared-branch lift at every even depth

Suppose \(e=2m\) and \(p\equiv3\bmod4\). Work over
\(\mathbb Z_p\) with \(Y=1\) and exact
\(x_0=-2/\rho\), so \(q_1(x_0)=0\) and
\(q_1'(x_0)=4\rho\) is a unit. The first changed tangent
at \(x_0\) is exactly \(-\epsilon/3\), while its opposite
is \(-4/7\bmod p\). Therefore \(q_2(x_0)\) has valuation
exactly \(2m\). The second quadratic also has simple roots
modulo \(p\) (as in the original disjoint/shared-branch proof),
so \(q_2'(x_0)\) is a unit.

At \(x=x_0+p^{2m}\zeta\), the two exact scaled residues
\(p^{-2m}q_i(x)\bmod p\) are consequently affine linear
polynomials in \(\zeta\bmod p\) with nonzero slopes and
distinct roots: the first has constant 0, the second a
nonzero constant. Outside their two roots the sums of the
two individual characters each have absolute value at most
1, and their product sum also has absolute value 1 by the
separable quadratic character identity. Hence at least
\((p-5)/4>0\) choices make both residues nonzero squares.
Using that \(2m\) is even, unit Hensel gives actual two
square roots of \(q_i(x)\). This lifts a point in the shared
branch and realizes the distinct unit class \(-1/7\).

Finally, within each admitted class the base point does lift
to the particular \(D_\tau\): use the two genuine conic
parameters and adjust their relative scale by a local square
root. This verifies sufficiency for the named cover, not just
existence of residue values on the base curve. In particular
actual \(p=83,e=1\) remains an exact obstruction to the other
unit class, while the split/even condition would be new for
any such prime found in the same \(L'\).
