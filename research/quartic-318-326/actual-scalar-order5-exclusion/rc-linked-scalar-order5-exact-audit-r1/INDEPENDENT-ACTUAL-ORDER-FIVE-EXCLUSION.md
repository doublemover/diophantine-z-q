# Independent exact audit: moving order-five H/L′ locus excluded

This is for the previous fixed h,J. Exclude the fixed support of
\(2\cdot3\cdot5\cdot7\cdot R\cdot(1+A)\cdot\beta\).
The locus means **both** source reductions \([h]R_0\) are killed
by 5 and at least one is nonidentity, over the split embeddings
or quadratic residue field. No higher/mixed orders are covered.

The literal translated \(i=mh\) has \(v_5(m)=8\). Therefore both
translated arms reduce to identity. On any active arm
\(U=2y/(x^2+d^2)\) is a finite nonzero residue: its vanishing would
give 2-torsion, and a denominator pole would double to the nonzero
\((0,0)\), giving order 4. That arm's ratio \(U_i/U_h\) vanishes.
On a formal identity arm the ratio is integral (not necessarily
zero) by the formal linear term. Hence the norm ratio vanishes,
\(W=N^2\), and an identity arm contributes 1 to \(N\).

For \(x=dX,\ t=5X\), \(U^2=20t(t^2-25)/(d(t^2+25)^2)\).
The odd division recurrence gives
\(\psi_5(X)=5X^{12}-62X^{10}-105X^8+300X^6-125X^4+50X^2+1\)
on \(y^2=x^3-x\). Its monic version is \(g=5^{11}\psi_5(t/5)\),
and \(g=(t^2+25)q+r\) with \(r=-512\cdot5^{11}\).
Thus the residue inverse square is \(q^2/r^2\). With \(S=7Rr^2\)
use the fourth power \(w=(S(1+U^2/R))^4\) in the monic quotient.
The denominator uses only fixed units, since
\(d^{-1}=(3+\sqrt2)/7\) on one branch and its conjugate on the other.
The second degree-12 characteristic polynomial is conjugate;
if one branch is O, its value is \(S^4\). Compare active pair
products \(w_1w_2\), or one-active \(wS^4\), after multiplying
by \(144\beta\) for H and \(7056\beta\) for L′, against
\((1+A)^2S^8\) and \(48(1+A)^2S^8\), respectively.
Each actual allowed congruence therefore forces a root of the
corresponding full determinant. This test includes inert primes
by specialization into the algebraic closure of their residue field.

At the stated good primes the raw base point is affine and
\(\psi_2=4\sqrt2\) is a unit. The reduction criterion is
[Naskręcki–Verzobio, Proposition 3.9](https://doi.org/10.1017/prm.2024.7).
Both coefficients in the quadratic integer ring vanish precisely
when both split branches vanish or the inert element vanishes.
Intersect the entire saturated determinant with both coefficients
of \(\psi_{5h}\), then remove the **whole support** of the gcd
with both \(\psi_h\) coefficients. This removes only the identity-only
primes from the possible locus, not primes with one active arm.
Using a normalized \(\psi\) has no effect on zeros because
\(\psi_2\) is a unit.

The supplied Node replay passed. An independent Python replay uses
traces of actual power matrices for the characteristic polynomial
and the plain division-polynomial recurrence with \(\psi_2^{-1}\).
They agree on all bit lengths, gcds and saturated residual integers.

| target | determinant bits raw/saturated | gcd at 5h | identity gcd | residual |
|---|---:|---:|---:|---:|
| H | 189557 / 80395 | 1495733306972434451 | 2870889264822331 | 521 |
| L′ | 190496 / 80191 | 43002467399 | 27281 | 1576279 |

Here \(1576279=89^2\cdot199\). The three survivors are prime by
trial division. Independent source group arithmetic gives active U
respectively 510,9,8 and W respectively 104,88,61. Thus the only H
candidate has \(D=237\ne1\) mod 521, and the two L′ candidates have
\(F=18\) mod 89 and \(F=166\) mod 199. None is actual in the stated
locus. No full scalar expansion, interval prime scan, rank theorem,
or Lean claim. The two determinant replays recompute exact BigInts;
their outputs are summarized, not full expanded integers.
