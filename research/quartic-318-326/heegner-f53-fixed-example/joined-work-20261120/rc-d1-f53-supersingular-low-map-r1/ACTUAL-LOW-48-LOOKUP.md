# Complete mod-53 low-level lookup, with marked-address guard

The field is exactly `k = F53[u]/(u²−22)`; tuples `[a,b]` mean
`a+b*u`, with *this* u (not its Frobenius conjugate). This evaluates the
already chosen based degree-two low map `φ0 : X0(48) → E_−1`. It does
not reduce high-level modular points, select Weil roots, change the
trace normalization, or prove the 20-class sum nonzero.

## Model, true cusp, coverage

Use [Colò, Appendix A, pp. 247–248](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf#page=265):
`y²−(x⁴+1)y=3x⁴` with `T=x−2+3x/y`, `U=(y−2x−1)/x` for the
ordered t16 degeneracies at z and 3z. These are the genuine marked
forget-3 and quotient-by-3 maps, not just the source/target j-values.
The hyperelliptic model is smooth at 53: writing `2y−(x⁴+1)=Y'`, its
right side is `F=x⁸+14x⁴+1`; a common root with its derivative would
have `x=0` or `x⁴=−7`, where F is respectively 1 or −48. The monic
even-degree model also has two smooth points at infinity. The
smooth proper model (genus 3) matches the prime-to-level good modular
model by uniqueness of the stable model. This is not an identification
from a single modular solution. The ordered degeneracy functions are
reductions of the primary rational formulas.

Set `r=(x−1/x)/2`, `s=Y'/(4x²)`; then `s²=r⁴+r²+1`. Put
`A=(s+1)/r²`, `B=(A²−1)r`; the exact identity is
`B²=(A²−1)(2A+1)`, so `φ_raw=(2A+1,2B)` on
`Y²=X(X+1)(X−3)`. The ∞ cusp is the infinity branch with
`y/x⁴→1` from the q-leading term; it has `A→1,B→0`.
**Thus φ_raw(∞)=(3,0), and the based map φ0 sends ∞ to O.**
Translate by the same `(3,0)`. When `φ_raw=(X,Y), X≠3`, use
`m=Y/(X−3)`, based coordinate `V=m²−1−X`, and based ordinate
`m(3−V)`. When raw equals (3,0) the based point is O. The order
of the two edges in `(T,U)`, and the sign of the ordinate, matter.

The finite search is exhaustive over k and independently certifies
it covers *all geometric* supersingular marked objects:
* Hasse criterion on a Legendre model: the `X^52` coefficient of
  `(X(X−1)(X−λ))^26` is, up to sign, `∑ binom(26,i)² λ^i`.
  It has 26 distinct roots in k, none 0 or 1. Every geometric
  elliptic curve in characteristic 53 admits the Legendre model,
  so evaluating its j-map at those roots gives the complete
  supersingular j-list: 0, 46, 50, 28+21u, 28+32u.
* On a geometric curve above each j there are exactly 24 cyclic
  order-16 subgroups (192 generators divided by 8) and 4 cyclic
  order-3 subgroups. For j≠0,1728, the only automorphisms ±1 fix
  the subgroups. At j=0 the extra effective group of order 3 acts
  freely on the nonzero order-2 point underlying a cyclic C16,
  so the number of pairs up to automorphism is 32 instead of 96.
  j=1728 is not supersingular. This gives exactly 416 geometric
  X0(48) points over the five j-values.
* For every k-value x, the full list of solutions y is recovered
  by the finite square-root table for `F(x)`, including a repeated
  square root once. The lookup finds precisely the expected
  `32+4·96=416` distinct smooth noncuspidal chart points above those
  j-values. Source j is evaluated through the ordered t16→t8→t4→t2
  chain, first arrows `v²/(v+c)` for c=2,4,16. See the same
  primary figure. Therefore no other chart, field, arbitrary choice
  of underlying model, or actual C16,C3 object is missing.

## Exceptional scope and exact interface

`LOW-48-SUPERSINGULAR-F53.json` is the table. Every one of its 416
ordered `(T,U)` keys has a single solution `(x,y)`, and a single
based value. For direct online reconstruction substitute
`y=(U+2)x+1` in `(T+2−x)y=3x`, a quadratic, and filter by the
literal quartic and x,y≠0. Never use a plain unordered pair of j's.

Over the *whole* model the excluded affine cases are explicitly
listed in `chart_bad` (x=0,y=0 or 1) and `project_bad` (eight
further affine points projecting to a cusp); the two points at
infinity are also outside this chart. E.g. (1,3) is an affine
cusp, **not** the chosen ∞ cusp, and uses the `r=0,s=+1` limit.
In general r=0 means x=±1. On the r=0,s=+1 branch raw is O and
based is (3,0); on r=0,s=−1 use
`A=(r²+1)/(s−1)→−1/2`, giving raw (0,0) and based (−1,0).
There is no zero denominator, r=0 branch, or raw=(3,0)
among the 416 actual supersingular records.

An ordered list of **four adjacent t2 values alone**, even on *both*
sides of the 3-isogeny, is weaker than the ordered pair of actual
t16 coordinates: there are precisely 12 ambiguous two-branch keys
(24 rows), and their two based values always differ. The t3 labels
at all four corresponding positions still coincide within each
branch pair. The exact collisions are in `chain_collisions`.
For an adaptive alternative, each ambiguous key is resolved by
one indicated genuine *marked t4* on the original side. If an
actual point P4 generates that cyclic 4 subgroup, x0=x([2]P4)
on the short curve and v=x(P4)−x0, then `t4=64v/(3x0−2v)`.
Indeed translation by x0 gives a=3x0 and b=v²; the two actual
2-coordinates are `256/(k²−4)` and `1024(k+2)/(k−2)²`,
k=a/v. Those are the ordered degeneracies of the displayed t4,
and generic uniqueness yields the same function in special fibers.
This is one local extra input only for collisions, not a new
high-level kernel or orientation requirement. Computing both true
t16 inputs directly avoids it.

## Independent exact first-orbit check

`lookup.py` rebuilds the full low-level table from scratch in
roughly one second, no externally loaded tables. `audit_class.py`
uses independent short-cubic addition after checking all 288
component unit pairs and their exact signed low-map values against
the table. The frozen first-class receipt reproduces the raw based
sum `(24+44u,12+26u)`, and `[224]` is `(22,15u)≠O`
killed by 13. There are only 203 distinct ordered low-level
addresses in this **one** class, so deduplicating the 288 rows is
wrong. That residue check authenticates the low values given the
supplied ordered marks; it neither verifies the supplied field
transport nor prevents cancellation against the 19 other classes.
