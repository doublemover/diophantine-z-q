# A conductor-one detector on the smaller semistable base

This strengthens the higher-level \(h=-9239\) route (9046d7c1)
without changing any of the original detector equations, the
chosen same-scale pair, the marked Selmer class, or the conditions
on the three new Gaussian primes. It constructs a smaller fixed
modular-curve target, not a numerical Heegner trace or a rank-one
claim for an uncomputed \(D\).

## 1. The lower semistable model and exact fixed even donor

Set \(r=407\cdot2399=976393\), and define
\[
 E^\flat:\ y^2=x(x+76768)(x-407),\qquad
 N^\flat=2\cdot3\cdot5\cdot7\cdot11\cdot37\cdot2399=205042530 .
\]
The old same-scale base \(E_*\) is precisely its \(r\)-twist,
as multiplying the two indicated roots by \(r\) shows. Hence
the selected odd \(E_D\) is exactly \((E^\flat)^{rD}\).
The fixed lower model has split multiplicative reduction at
\(2,7,37\), nonsplit multiplicative at \(3,5,11,2399\), good
elsewhere, so it is semistable with the displayed conductor and
\(W(E^\flat)=+1\). At 2 the simple scale \(x=4X,y=8Y+4X\)
gives the same split node proof as before. At odd primes the
discriminant and tangent give the signs with unit \(c_4\).
The character \((r/61)=+1\) ensures the same reduction target at 61.

Take the fixed prime fundamental discriminant \(h'=-2207\),
coprime to all conceivable selected \(D\) and to \(r\).
It is \(1\bmod8\), has signs \(+,-,-,+,-,+\) in the fixed order
\(3,5,7,11,37,2399\), and is nonsquare at 61. The exact ordinary
2-descent on \((E^\flat)^{h'}\) has dimension four. The two
rational torsion rows together with the two explicit triples
\[
       L=(26389,83965,385),\qquad R=(-177526,-23990,185)
\]
are a basis in the root order \(0,169426976,-898249\).
The precise all-place check is as follows.

* Outside the fixed \(-1,2,3,5,7,11,37,2399,2207\), the full
  rational 2-torsion unramified image imposes zero valuations.
  At the real place the sign at the minimum root (third
  coordinate) is positive. At 2 the same two torsion points
  and \(x=S+640\) on the untwisted lower base give exactly
  the eight classes with third coordinate square; transport
  by \(h'\) being a local square.
* At 3,5,7 the collision is of the second and third roots
  at depths 2,2,3, and split only at 5. The resulting local
  images are respectively all unit triples, the tuples
  \((1,d,d)\), and the depth-odd nonsplit table allowing
  valuations \(000,011\) with the separate unit sign
  positive, negative respectively.
* At 11 and 37 the collision is \(0\) and the third root,
  depth one and nonsplit; at 2399 it is \(0\) and the
  second root, likewise depth one and nonsplit. Apply
  the same two-root rule. At 2207 the four rational torsion
  rows exhaust the image, as the three pair differences
  all have depth one and the torsion valuation rows
  distinguish the four classes.

The exact local annihilators have rank 14 on 18 global
coordinate bits, and the displayed triples give the two
independent essential classes. Their Cassels product is
\(-1\), with local negative signs exactly at \(\infty,2,2399\).
The three **primitive rational tangent seeds** (omitting a
successive root projection) are
\((39,1148,30989),(9,877,92),(1,207,107)\), with coordinates
ordered as in 9046d7c1. The verifier certifies them directly
on the exact conics, finite Hensel error bounds for each
tangent value, and genuine real square-root intervals for
the sign at infinity. Away from the supported places the
local tangent value has even valuation by the smooth
primitive conic tangent argument of 9046d7c1. None of
these is a local-sample surrogate for a global row.

The essential pairing is therefore nonsingular, giving
algebraic rank zero and \(\Sha((E^\flat)^{h'})[2^\infty]
\simeq(\mathbb Z/2)^2\), without assuming finite Sha.
The exact Cassels radical rule makes \([2]\Sha[4]=0\)
and excludes a divisible component. The separately authored
[Burungale–Tian rank-zero theorem A (v1)](https://arxiv.org/pdf/2611.11566v1#page=2)
applies to this full rational two-division field and gives
\(L((E^\flat)^{h'},1)\ne0\). This is a known-rank-zero
auxiliary, not a logical use of the unknown rank-one case.

## 2. Ramified-level conductor-one genus trace (no Gauss expansion)

Write \(d'=rD\) and \(K'=\mathbb Q(\sqrt{h'd'})\), a fundamental
negative discriminant (coprime \(h',d'\), both \(1\bmod4\)).
The primes \(2,3,5,7\) split in \(K'\), since their symbols for
\(h'r\) are all positive and the original \(D\) is square there.
The three other primes of the **squarefree** level \(N^\flat\),
\(11,37,2399\), ramify to exponent one in the discriminant.
The conductor-one genus character \(\psi'\) is the Hilbert
class character of \(K'(\sqrt{d'})/K'\), also cut out by \(h'\).
At a ramified level prime \(\ell\), evaluate it using the
unramified **\(h'\)** character:
\[
                \psi'(\mathfrak l)=(h'/\ell)=+,-,+,
                \qquad a_\ell(E^\flat)=-,+,- .
\]
The genus extension is unramified by the two coprime quadratic
discriminants (or tame local norm and residue field checks).
There is no use of a Kronecker symbol with numerator divisible
by the ramified level prime. These are exactly the generalized
hypotheses (1),(2) of [Cai–Shu–Tian, Theorem
1.1](https://msp.org/ant/2014/8-10/ant-v8-n10-p05-p.pdf#page=3):
conductor one, no inert level prime, and \(\psi'(\mathfrak l)
\ne a_\ell\) at every ramified level prime. The modular curve
is ordinary \(X_0(N^\flat)\), not a new quaternion algebra or
a ramified ring-class conductor. The exact height normalization
includes \(2^{-3}\) for the three ramified level primes;
that is a nonzero scalar, not a cancellation in the trace.

Choose a fixed oriented level ideal \(\mathfrak N^\flat\) in
\(\mathcal O_{K'}\): one chosen prime at each split factor
and the unique ramified prime at each of the other three.
Its quotient is cyclic of order \(N^\flat\), including at the
ramified factors (all exponents one). The unaveraged weighted
sum of the literal conductor-one CM points under an actual
based modular map \(\pi^\flat:X_0(N^\flat)\to E^\flat\) is
\[
       Q'=\sum_{\mathfrak c\in\operatorname{Cl}(K')}
                   \psi'(\mathfrak c)\pi^\flat(x_{\mathfrak c}).
\]
The Galois eigencurve of the trace is exactly \((E^\flat)^{d'}=E_D\).
For this phase check note that \(c\) conjugation takes the
level ideal to its conjugate, and the full Fricke involution
duals that level by the class shift by \(\mathfrak N^\flat\)
(or its inverse, immaterial to a quadratic character). This
still holds at ramified factors, since
\(\mathfrak l^2=(\ell)\).
At the split level factors \(2,3,5,7\) the genus values are
\(+,+,-,-\), of product \(+1\). At the three ramified factors
their product is \(-1\). The total level-shift sign is thus
\(-1\). Full Fricke on \(E^\flat\)'s differential has
eigenvalue \(-1\), since \(W(E^\flat)=+1\); multiplication of
these two signs is \(+1\). The constant cusp contribution
cancels against \(\sum\psi'=0\). Thus \(Q'\) lies over the
real quadratic \(\mathbb Q(\sqrt{d'})\) and is anti-invariant
there, exactly as required for the rational twist point.

The genus factorization is
\[
 L'(E^\flat/K',\psi',1)
           =L'(E_D,1)\,L((E^\flat)^{h'},1),
\]
and CST relates this derivative to the height of the literal
trace. At p61 the field \(K'\) is inert because \((h'/61)=-1\)
and \(d'\) is square there. The reduction of the full Hilbert
class orbit is accessible over \(\mathbb F_{61^2}\), as the
inert ideal is principal. The weighted sum reduces in the
rational group by the just-proved descent. Its exact order
is 68 at the level of the whole rational residue group.
**One nonzero \([4]\bar Q'\in E^\flat(\mathbb F_{61})[17]\)**
at an actual selected \(D\) therefore gives a rational
nontorsion on \(E_D\), and Gross–Zagier gives analytic rank
one on that same \(E_D\) without the rank-one 2-converse.
The good prime 13 excludes rational 17-torsion, since its
group order on the \(d'=rD\) twist is 12 (base order 16 and
\((r/13)=-1\)). No projection is claimed to be nonzero yet.

This replaces the high marked level \(N_*=rN^\flat\) by
\(N^\flat\) and needs **no** Gauss translation sum. The class
field discriminant size is larger by the constant factor
\(2207r/9239\) than in 9046d7c1; the actual class work remains
unresolved, and even the lower modular \(\Gamma_0\) index is
630374400. Thus this is a smaller exact map and a different
finite target, not a proof of tractable numerical enumeration
or a claim that any analytic nonvanishing theorem enforces
the selected ray. The same contact-cell and saturation
obligations remain after the arithmetic rank result.

## Replay

python3 -B check_low_even2207.py | cmp - EXACT-LOW-EVEN2207.json

The verifier reads only the exact adjacent witness JSON, using
Python standard library. No new primes in the marked \(D\)
were numerically selected and no class-group job was run.
