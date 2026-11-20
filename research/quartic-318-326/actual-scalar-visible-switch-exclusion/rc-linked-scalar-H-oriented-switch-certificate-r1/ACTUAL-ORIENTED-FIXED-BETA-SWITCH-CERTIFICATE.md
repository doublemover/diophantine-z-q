# Exact constructive test for any nominated orientation divisor of actual H

Fix the actual positive primitive coordinates \(Z,C\), with
\(H=Z^2-\beta C^2>0\) odd and \(\gcd(H,\beta)=1\).
The fixed \(\beta\) is squarefree and \(1\bmod8\).
Let \(d>0\) be a **unitary divisor of the actual full \(H\)** and
put \(t\equiv Z/C\pmod d\), which is a unit at every prime dividing
\(d\). Thus \(t^2\equiv\beta\pmod d\).
This is an exact equivalence for a **nominated** \(d\), not a
method for producing such a divisor from unfactored \(H\).

The companion norm representation with exactly the \(d\)
orientations reversed exists if and only if there are integers
\(x,y\) such that
\[
 x>0,\quad x^2-\beta y^2=d^2,\quad
 x\equiv t y\pmod d,\qquad \gcd(x,y,d)=1 .
\]
Here a companion must be positive integral and primitive, with
the same \(H\); orientations are relative to the original
\(Z+C\sqrt\beta\). No nonsquare/unit congruence replaces this
Pell identity. The criterion needs only the rational reduction
\(1/c\pmod d\), not the individual reduced \(Z,C\) modulo \(d\).

## Sufficiency and literal norm transport

Let \(F=\mathbf Q(\sqrt\beta)\) and \(A_d\) be the actual orientation
ideal of norm \(d\) with the full exponents of the original
\(\alpha=Z+C\sqrt\beta\). If \(q^e\Vert d\), its chosen branch
has \(\sqrt\beta\equiv-Z/C\pmod{q^e}\). Thus \(x+y\sqrt\beta\)
vanishes at that branch. The other branch is a unit: if both
vanished mod \(q\), then \(x,y\equiv0\) since \(q\nmid2\beta\).
The norm \(d^2\) forces the whole \(2e\) valuation at the chosen
branch there, and unit valuations at primes away from \(d\).
Consequently \((x+y\sqrt\beta)=A_d^2\).
Its generator is totally positive since \(x>0\) and
\(x^2>\beta y^2\). Multiplying by its conjugate divided by \(d\)
gives the literal integers
\[
 Z'=(xZ-\beta y C)/d,\qquad C'=(xC-y Z)/d.
\]
The congruence for \(x\) makes \(xC-yZ\equiv0\bmod d\), and
\(Z^2\equiv\beta C^2\bmod d\) gives the other divisibility.
The product identity has norm \(H\); its ideal differs from
\((\alpha)\) by \(\bar A_d/A_d\), so it remains primitive at
every \(q\mid H\), hence globally primitive.
Its real embeddings are both positive, so \(Z'>0\).
If necessary multiply by a sufficiently large positive power
of any positive integral norm-one Pell unit of \(\beta\)
to make \(C'>0\); the resulting element remains integral and
primitive with exactly the given orientations. This final Pell
multiplication normalizes the sign, not the independently
chosen switch.

## Necessity and the actual dyadic lattice

Given a companion \(\alpha'=Z'+C'\sqrt\beta\) with those
orientations, \((\alpha')/(\alpha)=\bar A_d/A_d\).
Then
\[
 u=d\,\alpha/\alpha'
\]
is a totally positive generator of \(A_d^2\), with
norm \(d^2\). It is integral in the maximal order because
\(A_d^2\) is integral. Write \(u=(X+Y\sqrt\beta)/2\), \(X,Y\)
integers of the same parity. The odd case gives
\(X^2-\beta Y^2\equiv0\pmod8\), contradicting
\(X^2-\beta Y^2=4d^2\equiv4\pmod8\).
Therefore both are even, \(u=x+y\sqrt\beta\) with integral
\(x,y\). The literal branch factorization of \(A_d^2\) now
forces \(x\equiv ty\bmod d\) and \(\gcd(x,y,d)=1\);
positivity forces \(x>0\).

The simpler \((20147941/d)=+1\) condition is a cheap rejection
test for this system, not a solution of it. At \(d=1\) one
obtains the original orbit; at \(d=H\), the conjugate orbit.
A certificate giving hidden-support progress must additionally
prove that both \(d\) and \(H/d\) contain unseen primes after
removing the four visible depth-one factors. No such
nomination or Pell certificate has been found for the fixed
scalar in this work.
