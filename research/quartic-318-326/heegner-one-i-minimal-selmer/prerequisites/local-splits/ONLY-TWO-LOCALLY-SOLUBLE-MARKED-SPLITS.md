# Only two locally soluble splits of the actual base marked cover

This is the literal base \(d=\beta P\) with
\(P=114649\cdot119851=13740797299\), not the paired companion
nor Joined's variable scalar. The previous exact marked cover
has \(\beta V^2=(A^2-P)(A^2-9P)\). The split squareclass list
was derived from \(\gcd(a^2-Pb^2,a^2-9Pb^2)\mid8P\) for
primitive integers \(a,b\). Put \(F=a^2-Pb^2\) and \(G=a^2-9Pb^2\).
For \(B\mid\beta\), \(D\mid 2P\) squarefree and common sign ε,
the split system in \(\mathbb P^3\) is

\[
 C_{\delta_1,\delta_2}: \quad
 F=\delta_1u^2,\quad G=\delta_2v^2,\qquad
 \delta_1=\varepsilon B D,\quad
 \delta_2=\varepsilon(\beta/B)D .
\]

This is a refinement of the actual marked cover, not an assumption
about the rank or the full Selmer group of another curve. Any rational
point on an indicated split curve gives a rational marked point
by \(A=a/b,\ V=Duv/b^2\), then the preceding exact formulas.
Over Q, \(b=0\) cannot occur: if \(a\ne0\), both δ's would be
squares, contradicting their product βD²; if \(a=b=0\) then
all coordinates vanish. The corresponding formula at \(a=0\)
also contradicts nonsquare β. This is independent of any
nonzero oriented theta residue.

## Exact local filter, both directions

At any rational prime a local point can be scaled so \(a,b\)
are integral and not both divisible by the prime: with all
coordinates primitive, \(a,b\) both divisible would force
\(u,v\) divisible as the δ's are squarefree. At all primes
not dividing \(2\cdot3\cdot\beta P\) the two diagonal
quadrics form a smooth projective genus-one curve modulo the
prime. Indeed a singular linear combination of gradients
with both coefficients nonzero gives \(u=v=0\), then \(a=b=0\)
as \(8P\) is a unit; if one gradient coefficient is zero the
same conclusion follows using that \(\delta_1,\delta_2,9P\)
are units. A smooth complete intersection of type (2,2)
has genus one, the finite-field Hasse bound gives a point,
and smoothness lifts it. Thus only the following finitely many
places need testing.

- At a prime \(\ell\mid\beta\) with \(\ell\mid B\), \(b\) is a
  unit and \(F\equiv0\bmod\ell\), so \(G\equiv-8P b^2\).
  The exact test is \((-8P\delta_2/\ell)=+1\).
  Conversely set \(b=1,u=1\) and solve \(a^2=P+\delta_1\)
  by Hensel, since the actual \(P\) is a square unit mod
  every β prime. Then \(G/\delta_2\) is a square unit.
  If \(\ell\mid(\beta/B)\), swap the roles with
  \(a^2=9P+\delta_2\) and the test \((8P\delta_1/\ell)=+1\).
- At \(\ell\mid P\), \(a\) is a unit iff \(\ell\nmid D\).
  Then both δ's must be square modulo \(\ell\), and choosing
  \(a=1,b=0\) suffices. Otherwise \(a\) is divisible,
  \(b\) is a unit and both valuations of F and G are one.
  Test the square symbols of
  \(-(P/\ell)(\delta_i/\ell)\) modulo \(\ell\)
  (the factor 9 for \(G\) is square). These conditions suffice
  using \(a=0,b=1\).
- At 2, \(P\equiv3\bmod8\). If both \(a,b\) are odd the
  valuations of F,G are exactly 1, whereas opposite parity
  gives valuations 0. Set \(t=2\) in the former case and
  \(t=1\) in the latter. The requirement \(v_2(D)=v_2(t)\)
  and the two square classes \(F/t\equiv\delta_1/t\),
  \(G/t\equiv\delta_2/t\bmod8\) are necessary and sufficient:
  all quotients are odd, so these are the exact Q2 square
  tests. Enumerate \(a,b\bmod16\).
- At 3, \(P\equiv1\bmod3\). If \(3\mid a\) then \(F\) is a
  nonsquare unit mod3, so \(\delta_1\) must be nonsquare; if
  \(a\) is a unit, \(G\) is a square unit and \(\delta_2\)
  must be square. Conversely if \(\delta_1\) is nonsquare
  take \(a=3\sqrt P,b=1\), giving \(F=8P\) and \(G=0\).
  If \(\delta_1\) and \(\delta_2\) are square take
  \(a=1,b=0\). This proves the exact disjunctive test.
- Over R choose \(a=1,b=0\) for the positive common sign
  or \(a=0,b=1\) for negative.

## Exact result on the fixed base

The counts are 4,096 candidate splits, 32 passing all β
places, 8 passing the two P places, 4 passing 2 and exactly
2 passing 3. They are everywhere locally soluble by the
constructive tests above:

| sign | \(B\) | \(D\) | \(\delta_1\) | \(\delta_2\) |
|---|---:|---:|---:|---:|
| − | 41579528353 | 119851 | −4983348052635403 | −589804149395 |
| + | 4921145 | 114649 | 564204353105 | 4767051346143097 |

Nothing here decides global solubility of either curve. The
relevant next problems are these two much smaller explicit
torsors (minimize the two rational quadric pencils, further
descent or verified height search), not every high index and not
just enlarging a raw √norm loop. Any success would still be
only the base \(q=119851\), not a paired witness or original
four-pole conclusion.

    python3 -B check_one_I_split_everywhere.py | cmp - EXACT-ONE-I-MARKED-SPLIT-LOCAL.json
