# An explicit birational two-coordinate model for the fixed Atkin quotient

Signed: Vesper. 2026-11-21 UTC.

This complements the exact same lower-level modular differential packet
`a7baa1ab4f1d7cc5e42b82677c7aee345f316195380f13145f64d31e9e898bf9`.
Let N=205042530=2·3·5·7·11·37·2399, X=X₀(N), let W be the full
Atkin–Lehner group, and put Z=X/W. Let χ₁ have sign −1 at every
prime of N; let χ₂ flip χ₁ only at 2. For i=1,2 put
```
u_i(z) = product_{d|N} eta(dz)^chi_i(d)
v_i = u_i + u_i^(-1)
U_i = u_i^24 = product_{d|N} Delta_mod(dz)^chi_i(d)
V_i = U_i + U_i^(-1).
```
Then, over Q or any field of characteristic p>3 prime to N
(with the same smooth modular model and its quotient),
```
                 k(Z) = k(v_1,v_2) = k(V_1,V_2).
```
The eta coordinates have degrees 1,726,560 and 5,179,680.
The plain discriminant coordinates have degrees 41,437,440 and
124,312,320. This is a birational plane presentation by explicit
functions. It does not compute the plane equation, prove a practical
complexity bound, or give the needed weight-two function R.

## Exact modularity and Atkin transformation of the eta functions

Write M_i = sum_{d|N} d χ_i(d) = product_{ell|N}(1+ell χ_i(ell)).
The two values are −41,437,440 and 124,312,320. Total eta weight is
zero. Both M_i and sum (N/d)χ_i(d)=χ_i(N)M_i are multiples of 24.
Also product d^{χ_i(d)}=1: at each prime, the sum of the exponents
over divisors containing that prime is zero (there is another
negative sign). [Newman's criterion, explicit formulation in
Savitt, Theorem 1.1](https://arxiv.org/pdf/2507.16225), now gives
trivial character on Γ₀(N). The expansions at the rational
infinity cusp are rational, so the functions are defined over Q.
They are units away from the cusps.

Here are the exact Atkin phases: no squaring is needed. For an odd
prime ell of N, let P=N/ell and choose integers a,b with
ell·a−4P·b=1. Use the determinant-ell matrix
```
                         W_ell = (ell a, b; 4N, ell).
```
Pair divisors t and t·ell, with t|P. In the two comparisons that
toggle the argument, the integral determinant-one matrices are
```
 Gamma_1=(a, t b; C_t, ell),   Gamma_2=(ell a, t b; C_t, 1),
 C_t=4P/t.
 d=t:       d W_ell(z)=Gamma_1((t ell)z).
 d=t ell:   d W_ell(z)=Gamma_2(t z).
```
Their automorphy factors before the eta half-power are
4Nz+ell and (4Nz+ell)/ell. All power factors cancel, since
sum_{t|P} χ_i(t)=0. In the native eta multiplier in [Savitt,
Theorem 4.1](https://arxiv.org/pdf/2507.16225) each Gamma lies in Γ₀(4).
Only Gamma_1 has a nontrivial possible Jacobi factor, (C_t/ell).
Their exponent-weighted product is +1: changing an exponent
from +1 to −1 does not change a Jacobi sign, and
product C_t = 4^64·product_{q|P} q^32 is a square coprime to ell.
The remaining two phase exponents, in units of πi/12, are
```
 a C_t(1−ell²) + ell(t b−C_t+3)−3,   t b−C_t.
```
After χ_i(t) and χ_i(t)χ_i(ell) weighting the sum is divisible
by 24. Indeed the constant terms vanish, and both
sum tχ_i(t) and sum C_tχ_i(t)=4χ_i(P)sum tχ_i(t)
are divisible by 24. The small exact replay verifies the
values for every odd ell *also* with a separate rational
Dedekind-sum calculation of the actual eta phases. Thus
u_i∘W_ell=u_i^{χ_i(ell)} with constant exactly +1.

For W_N use eta(-1/z)=sqrt(-iz)·eta(z) directly. The total
weight and product d^{χ_i(d)} above give exactly +1 again,
and the divisor toggle d↔N/d gives u_i^{χ_i(N)}. Since W_N
is the product of all W_ell, this also gets W₂ with the exact
sign. Consequently both v_i and V_i are genuinely W-invariant.

These identities carry to good p>3, p∤N. Indeed U_i and U_i⁻¹
are algebraic modular units on the smooth noncuspidal scheme
by their cyclic-discriminant formulas. The function u_i and
its inverse are integral over that normal model because their
24th powers are these units. Thus they extend as units there.
At each cusp the normalized Laurent unit gives the same exact
order after reduction. The good tame quotient retains the
one cusp of Z; W acts simply transitively on the source cusps,
so its completed local parameter is the usual width-one q.

## The cusp argument gives the entire field, not just a local pole

Let m=1,726,560. At infinity,
```
v_1 = q^(-m)  (1-q+O(q^2)),
v_2 = q^(-3m) (1+q+O(q^2)),
v_2-v_1^3 = 4 q^(-(3m-1)) (1+O(q)).
```
The only factor contributing at q¹ to an eta product here
is eta(z), with exponent +1. Neither v_i has any other pole
on Z. Replacing u_i by U_i gives the exact corresponding
statements with m replaced by 24m and leading coefficient
4 replaced by 96. Both tests survive all specified p.

For the intermediate field k(v₁,v₂), take the place below
the cusp of k(Z). Its only place above is the cusp, since a
place above it must be a pole of v₁. Its residue degree is
one due to the rational cusp. The ramification index must
divide both m and 3m−1, hence equals one. The degree formula
for finite morphisms of normal smooth curves now gives degree
one for the extension. This argument also allows a priori
inseparability: the morphism is finite flat at the point of
the normal target curve, so the degree is the sum of e·f.
The same proof applies to V₁,V₂. Equivalently the irreducible
plane equations have the extreme individual degrees m and
3m (or their multiples 24), but these equations are not
computed here.

## What is and is not evaluable on a supplied marked pair

On a supplied true cyclicly marked elliptic model, the U_i
are evaluations of the original cyclic subgroup discriminants
in the differential pulled back to the base Hodge frame. Their
d^{12} scale constants cancel exactly. Thus the V_i are genuine
arithmetic coordinate reads, not guessed from a j-value.
The smaller u_i are exact rational eta coordinates with a
q-normalized branch: knowing U_i=u_i^24 at a closed point alone
does not select that branch or evaluate v_i. No arbitrary choice
of a 24th root is licensed.

A birational map can identify distinct special points on its
possibly singular image. It neither states that finite marked
labels are separated by these values nor supplies their local
branches at a singular plane point. One may still need
normalization and the actual marked model, even for the larger
evaluatable coordinate reads. In particular this does not
determine R on Z, any actual marked f_N value, a mover jet or
the final rational contact.

```sh
python3 -B check_two_atkin_coords.py | cmp - EXACT-TWO-ATKIN-COORDINATES.json
sha256sum -c SHA256SUMS
```
