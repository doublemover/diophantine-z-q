# The actual split dual forces a new odd-depth discriminant prime

Use the same fixed literal scalar \(c=C/Z\), \(\beta\),
\(D=\beta c^2\), \(\delta=1-D\), and \(F=49D-48=L'/Z^2\)
as the reviewed alternate quartics. Here \(C,Z\) remain the
actual reduced numerator and positive denominator. This proof
does not evaluate \(Z\) or run another support scan.

The alternate genus-one curve has Jacobian
\[
  E:y^2=x(x^2+A x+K^2),\quad
  A=\beta(25D-24),\quad K=12\beta\delta.
\]
Its dual under the quotient by \((0,0)\) is
\[
  E':y^2=x(x-\beta D)(x-\beta F).
\]
Indeed \(A+2K=\beta D=(\beta c)^2\) is a square and
\(A-2K=\beta F\). Thus both nonzero roots are rational and
the dual constant coefficient \(B'=A^2-4K^2\) has exactly
the same squareclass as \(\beta F\). This is the actual
rational x-class of the 2-torsion point \((\beta F,0)\).
Denote its signed squarefree representative by \(\eta\).

## A forced actual hidden prime, independently of denominator phases

The exact scalar has \(\nu_2(F)=5,\ \nu_3(F)=1,\ \nu_{83}(F)=1\).
At 2, \(c/4\equiv19\bmod64,\ \beta\equiv9\bmod16\), and
\(F/32=(49\beta(c/4)^2-3)/2\equiv7\bmod8\).
At 3, \(3\mid c\) and \(F/3\equiv-16\bmod3\).
The actual 83 row gives \(F\equiv81\cdot83\bmod83^2\).
At every \(p\mid\beta\), \(F\equiv-48\bmod p\) is a unit.
Actual 7 has \(F\equiv1\bmod7\). At any other odd prime of
\(Z\), \(F\) has negative even valuation and \(\beta F\) is
a local square: factor \(49(\beta c)^2\) from \(\beta F\),
and the remaining correction is \(1\bmod p\).
Since \(F<0\), it follows that
\[
 \eta=-6\beta\,83\,M,\qquad
 M=\prod_{\substack{q\ne2,3,83\\ q\mid L',\ \nu_q(L')\ {\rm odd}}}q.
\]
All primes of \(M\) are outside \(\beta\) and 7. They are
actual odd-depth primes of the new discriminant, not free
parameters. In particular \((3\beta/q)=1\) for each \(q\mid M\).

At the actual prime 131, \(D\equiv1\), \(F\equiv1\)
and \(\beta\) is square; thus \((\eta/131)=+1\). But
\[
     (-6\beta\,83/131)=-1,
     \qquad\text{so}\qquad (M/131)=-1.
\]
Consequently **there exists an additional actual prime
\(q\mid L'\), with odd valuation and \((q/131)=-1\)**.
It lies above 20 million by the exact earlier scan. This
is an existence theorem about the actual integer, not just
a plausible unsearched factor or an assertion of its value.

The same local unit comparisons give the following further
constraints on the actual hidden product:
* \(M\equiv1\bmod24\), by the \(\eta\) units at 2 and 3.
* \((M/p)=+1\) at \(p=6551,2470991,16782959\), by the
  three other actual \(D=1\) rows.
* For \(p\mid\beta\), \((M/p)=(166/p)\) by comparing
  \(\eta/\beta\) with \(F\equiv-48\bmod p\).
  The only negative signs are at 163 and 733.
* \((M/7)=-1\) from actual \(F\equiv1\bmod7\), and
  \((M/83)=+1\) from the exact normalized 83 residue below.

Let \(k_0=5\cdot11\cdot163\cdot733\cdot1489\cdot6551
                         \cdot2470991\) be the previous
known-matrix kernel product. The product of the displayed
\(M\)-signs over this support is \(+1\); since \(M\equiv1\bmod4\),
reciprocity gives \((k_0/M)=+1\). The existing search excluded
new \(L'\) support with \((k_0/q)=+1\) through 120 million.
Therefore either some hidden prime is above 120 million,
or there are at least two hidden primes in the unscanned
complement \(20\,{\rm M}<q\le120\,{\rm M}\) with symbol
\((k_0/q)=-1\). In particular if \(M\) is a single prime,
it is above 120 million and is \(1\bmod24\).
The symbol at 131 forces at least one hidden prime with
its minus sign; it does not say this is the same one above
120 million when several factors occur.

## Exact local x-class table and orientation of the next cover

Use x-class 1 at infinity and the quadratic factor's constant
coefficient at \((0,0)\). Write \(\alpha_E,\alpha_{E'}\) for the
two images. The conventions are fixed by the actual isogeny:
\(E\to E'\) has \(x'=x+A+K^2/x=y^2/x^2\), and the raw
dual scales \(x''\) by \(1/4\) to get \(E\).
Thus \(\ker\alpha_{E'}=\operatorname{im}(E\to E')\) and
\(\ker\alpha_E=\operatorname{im}(E'\to E)\).
For the converse at a nonzero abscissa, a square \(x'\)
makes the discriminant of \(x^2+(A-x')x+K^2=0\) square
by the target equation; choose the root and ordinate sign
to match the target. At \((0,0)\) the same condition is
the splitting of that quadratic with \(x'=0\).
The dual has the identical argument and a square scale.

The useful exact index identity over \(\mathbb Q_p\) is
\[
 |\alpha_E|\,|\alpha_{E'}|=4\,|2|_p^{-1}.
\]
Indeed \([E:2E]=|E[2]|\,|2|_p^{-1}\) from a sufficiently
deep formal group and the finite quotient (or its snake
sequence). The kernel of \(E'/\varphi E\to E/2E\) has
order \(4/|E[2]|\), since the dual kernel is order two
and its intersection with \(\varphi E\) is
\(\varphi(E[2])\) of order \(|E[2]|/2\). This proves
the formula at odd primes and at 2, with no Sha
or rational rank premise.

At \(p\ge5,\ p\nmid\beta\), positive integral discriminant
and scalar depths give:

| Local set | \(\alpha_E\) | \(\alpha_{E'}\) |
|---|---|---|
| \(v_p(\delta)>0\) | all four | trivial |
| \(v_p(F)>0\) odd, or \(v_p(F)>0,\ p\equiv1\bmod4\) | trivial | all four |
| \(v_p(F)>0\) even, \(p\equiv3\bmod4\) | both units | both units |
| \(v_p(c)>0,\ (3\beta/p)=+1\) | trivial | all four |
| \(v_p(c)>0,\ (3\beta/p)=-1\) | both units | both units |

For the first row \(A\equiv\beta\) is square, as \(D=1\)
forces \(\beta\) square, and \(x=pu\) gives either odd
valuation class via \(y^2=x^2(A+x+K^2/x)\).
For the middle rows \(K^2\) is unit square. A nonunit
abscissa or one of negative valuation has square class 1
by dominance. A nonsquare unit abscissa can only lie
near \(r=-A/2\), in \(x((x-r)^2-\Delta/4)\) with
\(\Delta=A^2-4K^2\). Odd \(v_p(\Delta)\) precludes
it by competing even and odd valuations. For even
positive depth and nonsquare \(r\), choose
\(x=r+p^{v_p(\Delta)/2}t\) with
\(t^2-\Delta/(4p^{v_p(\Delta)})\) a nonsquare unit;
the quadratic character sum \(-1\) ensures such \(t\).
At \(F=0\bmod p\), \(r\) has class \(-1\),
and \(v_p(\Delta)=v_p(F)\).
At \(c=0\bmod p\), \(r\) has class \(3\beta\), and
\(v_p(\Delta)=2v_p(c)\). In the two-unit dual case,
\(B'\) has even valuation and \(A'=-2A\) is a nonsquare
unit (its class is precisely \(r\)). For
\(0<v_p(x)<v_p(B')\) the dual square equation is
impossible by the nonsquare leading coefficient \(A'\)
in \(y^2=x^2(x+A'+B'/x)\); for
\(v_p(x)\ge v_p(B')\) an odd valuation is also
impossible by constant-term dominance (the equality
case has even \(v_p(x)\)). The index identity then
forces exactly both unit classes. This covers the signs
and parities of all the displayed middle rows.

At \(p\mid\beta\) the actual \(c\) is integral,
\(K\) has depth 1, and \(A\) depth 1. Values other
than \(v_p(x)=1\) give square \(x\) by dominance.
For \(x=\beta u\) with unit \(u\), the reduced
quadratic in brackets is \((u-12)^2\), so unless
\(u\equiv12\) there is a forbidden odd valuation.
The attainable nonsquare class is \(3\beta\), attained
by the actual order-four point of \(E\). Thus
\(\alpha_E=\{1,3\beta\}\) and
\(\alpha_{E'}=\{1,-3\beta\}\), the latter by index
and its literal torsion class.

At 2 and 3 the exact rows are
\[
 \alpha_E(2)=\{1,3\},\quad \alpha_{E'}(2)=\{1,5,6,14\};
 \qquad
 \alpha_E(3)=\{1,-3\},\quad \alpha_{E'}(3)=\{1,3\}.
\]
For 2 scale \(x=4X\) and write the new quadratic as
\((X-k)^2+m^2 X\), \(k=K/4\equiv3\bmod8,\ v_2(m)=1\).
At \(v_2(X)\ne0\) the correction to \(X(X-k)^2\)
has depth at least three. For \(X\equiv1,5\bmod8\)
the quadratic after division by 4 has residue \(1+X\),
of valuation one. For \(X\equiv7\bmod8\) the square
test after extracting \(m^2X^2\) sees \(1+4\bmod8\).
Thus only classes 1 and 3 can occur, with 3 attained
by the known order-four point. On the dual after the
same scale, its roots are 4 and 0 mod 8, so \(X=5\)
gives a unit square cubic. The other generator is its
torsion class 14, proving the dual row by index.
At 3, \(v(A)=1,\ v(K)=1\). Only \(v(x)=1\) can
give a nonsquare class; putting \(x=3u\) forces
\(u\equiv2\bmod3\) since the inner reduction is
\((u+1)^2\). The known \(K\) attains \(-3\).
The dual torsion has class 3, giving its exact row.

For 83 in particular the compact \(\bmod 83^2\) replay
gives \(D=6746,F=6723,A=469\).
The original node is \(x=56\), and its x-class image
is trivial. On the dual,
\[
  -2A\equiv58,\quad B'/83\equiv7\bmod83;
  \qquad (x,y)=(5,9)\bmod83
\]
is an exact nonsquare-unit witness, lifting by unit
Hensel. The other generator is the actual dual torsion
class \(83\) because 7 is square. This confirms
all four classes and the sign of \(M\) at 83.

To compare with the reviewed next cover, the degree-two
morphism \(D_\tau\to C\) induces an isogeny on Jacobians.
Since \(E\) has just one rational nonzero 2-torsion
point over \(\mathbb Q\) (its other-root discriminant
is negative), the dual isogeny is the quotient by
that point; hence \(J(D_\tau)=E'\) and the map back
is the \(\alpha_E\)-kernel above. Over a local field
fix one lifting point on the base curve and its lift.
The image of possible relative-scale squareclasses
is the coset of \(\alpha_E\) obtained by translating
that point: this is the exact boundary map for the
isogeny (or translate the finite étale double cover
by the chosen torsor points). The twists indexed by
\(\tau\) change that boundary by their ratio class,
as seen by scaling the second parameter pair by a
square root. At 83 the nonshared tangent gives initial
\(\lambda=\tau/Z=1/7\); the group is trivial, so
changing the base point cannot change this class.
Accordingly the matrix row really is
\((\tau/83)=-(Z_{\rm exc}/83)\), since
\((Z_0/83)=-1,\ (7/83)=+1\). The exact dual table
does **not** remove this unknown phase.

## Global torsion pairing explains the redundant aggregate

Normalize \(\tau\) with all its already-known fixed-place
tests and set \(t=7\tau Z>0\). The global dual torsion
class \(\eta=\operatorname{sf}(\beta F)\) gives
\((t,\eta)_p=(7\tau Z/p)\) at odd-depth \(L'\) primes,
and a trivial Hilbert symbol at the even-depth \(L'\)
primes, even when their local row is nontrivial.
At \(H\) and \(Z\) primes \(\eta\) is square.
At \(C\) primes away from the fixed support both
arguments are units. At \(p\mid\beta\) it gives
\((7/p)\), since \(\tau Z\in\{1,3\beta\}\),
\(\eta=-3\beta\) locally, and \((a,-a)=1\).
Their product is \((7/\beta)=+1\).
At 2, \(t\) has class 1 or 3 and \(\eta\) class 14;
\((3,14)_2=+1\). At 3 and 7 the symbol is also
trivial by their unit residues just computed; at
infinity \(t>0\). Hilbert reciprocity therefore gives
exactly the formerly redundant product of odd-depth
\(L'\) rows. It is the global *rational torsion* class's
relation, not one new independent row or a global
obstruction.

The adjacent exact local-image filter also shows that
with dual support restricted to \(-1,2,3,\beta,83\),
the only class passing the already-known small and
four \(H\) tests is 1 (4096 masks to one). This is
not a computation of the full dual Selmer group:
the actual \(\eta\) just proved has more support.
Any separate useful dual test must take this into
account rather than assuming the visible 83 supplies
a global independent probe. No marked rational point,
full lift, or reduced-denominator character follows.

Replay: `python3 check_dual_hidden_prime.py | cmp - DUAL-HIDDEN-PRIME.json`.
The only Python input file is the exact sibling 83 row.
