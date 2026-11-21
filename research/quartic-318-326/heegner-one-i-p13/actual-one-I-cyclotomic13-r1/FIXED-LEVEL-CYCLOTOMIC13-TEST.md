# One exact cyclotomic leading-term certificate on the same original twist

Fix p=13, the actual base E₀=E₋₁ of conductor 48, and
the actual historical one-I d=2811626664334219040035976315.
The odd, primitive quadratic character is χ=χ₋d of conductor d.
This is a **sufficient finite residue test**, not a computed nonzero
value at d. The exact calculation below is validated on bounded
positive and null controls. It uses neither prior finiteness of
Sha nor the full short weight-3/2 theta coefficient.

## 1. Exact integral symbol of the original level 48 form

Manin generators are the 96 points of P¹(Z/48), written as
primitive bottom rows (c,e) modulo multiplication by units.
They represent oriented paths from g0 to g∞, with determinant
one. The order-two and order-three relations come from
(S=(0,-1;1,0)) and (R=(0,-1;1,-1)). The odd involution sends
the bottom row to (−c,e) and multiplies the functional by −1.
The code constructs all these rows over Q, then imposes the
actual good-prime Hecke eigenvalues at 5,7,11 from explicit
point counts on E₀: −2,0,−4. For each (ell) the correspondence
sends a path to the sum of paths under (xmapstoell x) and
(xmapsto(x+j)/ell); these are the ordinary prime-to-level
weight-two matrices. Endpoints are evaluated by exact
continued-fraction decomposition into determinant-one edges.
The selected rational dimensions are 5,3,3,1. Thus the
remaining primitive integer vector is a nonzero scalar
normalization of precisely the *odd* symbol of the given
lowest form f₀, not an arbitrary residue-valued vector
or the later level-2544 lift. Let (I_0(r)=int_infty^r 2πi f_0(z),dz).
The selected integer function Φ₀⁻(r) is proportional to
(I_0(r)-I_0(-r)) by one fixed nonzero scalar.

For the odd quadratic twist, the Gauss translation identity is
(f_d(z)=	au(chi)^{-1}sum_bchi(b) f_0(z+b/d)).
Applying it to (I_d(r)+I_d(-r)) sends the (I_d(-r))
summand by (bmapsto-b) to the negative of the conjugate
one, precisely because χ is odd. Thus the actual plus
symbol of f_d, up to a fixed nonzero scalar for each d, is

```
Φ_d^+(a/m) = Σ_{b mod d} χ(b) Φ₀⁻(a/m+b/d).
```

This normalization is integral by construction. Its scalar
comparison with a chosen Néron period need not be a 13-unit:
we use nonzero Taylor order over Q₁₃, which is unchanged by
any nonzero scalar. In particular no assumption about an
unknown Manin constant or a unit-leading-term BSD
normalization is made. The twist identity keeps the actual
newform and original d.

## 2. The first coefficient really is one finite residue

Choose γ=1+13, and for a prime-to-13 unit a modulo 169 write
e(a) for its cyclotomic exponent in the quotient of order 13,
with tame Teichmüller factor killed. In exact integer arithmetic,

```
e(a) = [(a^12 mod 169 − 1)/13] · 12^(-1) mod 13.
```

The ordinary measure on a+p^nZ_p from the plus symbol uses
`α^(-n) Φ_d^+(a/p^n)−α^(-n−1) Φ_d^+(a/p^(n−1))`,
where α is the unit root of the actual Hecke polynomial.
See [the ordinary measure formula in Stein's computational note](https://wstein.org/papers/talks/2007-02-07-banff-bsd/papers/lseries.pdf).
At n=2 this gives the quotient of its power series whose first
coefficient is the weighted sum of these measures with weights
e(a). Reduction modulo 13 is enough: for each nonzero class
mod 13, the 13 different lifts a of that class have exponents
0,…,12, whose sum is 0 mod 13. The lower stabilization term
is therefore zero in the **first coefficient**, not in the
whole distribution.

The remaining double sum can be written exactly in one CRT row.
Put b mod d as above, r=ad+169b mod 169d. Then
χ(b)=χ(r) since 169 is a square, and
a=d⁻¹r mod 169. (Phi^-_0) is periodic under adding integers
(translation is in Γ₀(48) and fixes infinity). Consequently
the coefficient of T, in this exact normalization, is

```
a13(E_d)^(-2) ·
 Σ_{r mod 169d, gcd(r,169d)=1} χ(r) e(d^(-1)r mod 169) Φ₀⁻(r/(169d))
 mod 13.
```

Using the inverse convention for the cyclotomic variable changes
the linear term by a unit and not the nonzero test. The chosen
integral symbol, exact projective path basis and weighting are
frozen in the verifier; no value at denominator 13²d was
obtained by multiplying Hecke eigenvalues of the fixed form.
Neither Hecke recurrence nor the CRT writing proves efficient
evaluation of this signed sum for a large fundamental d.

## 3. Why this would settle the odd step, and what is missing

The actual root number of E_d is −1, so the constant cyclotomic
term is zero by ordinary interpolation; α≡−2 mod13 gives
no ordinary Euler-factor zero. The above coefficient being
nonzero mod13 would therefore certify Iwasawa order exactly
one at the trivial cyclotomic character. By
[Yan–Zhu, Theorem 5.2](https://arxiv.org/html/2412.20078v4#S5.SS1),
the rational cyclotomic main conjecture identifies that order with
the characteristic-ideal order of the ordinary Selmer dual.
Ordinary control gives the full rational base Selmer quotient
after specialization; its Q₁₃ dimension is no larger than the
characteristic-ideal order (length of the torsion module at T).
Together with actual odd 13-parity this gives s13(E_d)=1.
Their [Theorem 5.11](https://arxiv.org/html/2412.20078v4#S5.SS3)
then gives analytic rank one, and rational rank one with finite
Sha from the forward theorem. The hypothesis of irreducibility is
available from the exact full residual image. The rational
theorems suffice: the conditional integral BSD formula is
not being used.

The exact bounded tests compare literal double sums with the
CRT rewrite and check all 12 lower stabilization classes.
Positive d=11,23,35,323 have exact central zero and linear
residues 6,12,9,7; d=83 has exact central zero and linear residue
0, showing this is not a tautological nonzero test on odd twists.
The even-sign controls d=7,19 have nonzero central symbols
and are not run through the rank-one implication. A zero
linear residue does **not** imply rank >1, higher Taylor
order, or zero analytic derivative in characteristic zero.

For the literal actual d, the direct row count is
`156·φ(d) = 297163182123786370704998400000`.
Only the fixed level-48 eigensymbol has been constructed; no
cancellation algorithm or compressed certificate for that
enormous weighted row is supplied. This statement is an exact
finite alternative to the class calculation, not a runtime
lower bound on all schemes. Neither this coefficient nor the
class eigenspace in the companion note has been evaluated.

```sh
python3 -B check_cyclotomic13.py | cmp - EXACT-CYCLOTOMIC-CONTROLS.json
```
