# The complete literal order-three source locus has no moving H/L prime

This closes the exact previously unresolved locus in
3bd552a5, not the entire specialized norm obstruction for k0.
There is no interval scan, factorization of an unresolved
cofactor, extraction of a new prime, or expanded elliptic point.

Let R_+= (1+√2,2√2) on y²=x³−(3−√2)²x, with its conjugate
R_- on the conjugate model. Keep the exact h and i=mh,
where m is divisible by 3. Recall that the named locus
requires both h-source reductions killed by 3 and at least
one not O. By the degree-24 elimination result of 3bd552a5,
any moving H or L' prime in this locus divides the corresponding
literal integer T_H or T_L in the frozen
ORDER3-FIXED-RESULTANTS.json, after discarding only already
excluded fixed-prime factors. Their bit lengths are 10544
and 10528 respectively. The eliminant used here is the **whole**
integer T, not its extracted factors.

## Exact residue condition on the two rational coefficients

For n=h or 3h let e_n=a_n+b_n√2 be the exact normalized
even division polynomial ψ_n(R_+)/(2y(R_+)). Both indices
are even. At every moving p the chart has good reduction
and 2y(R_+) is a unit. Thus e_n vanishes on a given
residue component if and only if [n] of the actual
raw generator there is O. This is the usual division
polynomial multiplication criterion at a nonsingular
affine point, valid here even if a prime divides n:
the no-common-cancellation statement in
[Naskręcki–Verzobio, Proposition 3.9](https://doi.org/10.1017/prm.2024.7)
applies to the affine good source, so the division pair
represents the exact reduced endpoint.

If √2 is inert, equality to zero in F_p² is equivalent to
a_n≡b_n≡0 mod p, since 1,√2 is the field basis. If √2 splits
with roots ±s, both exact labels are O iff
a_n+b_n s=a_n−b_n s=0 mod p, equivalently both rational
coefficients are zero because 2s is a unit. Thus these
two coefficient conditions handle both modes at once, and
do not presume a split label or select one root over another.

For each literal T compute

    G = gcd(T, a_(3h), b_(3h)),
    G0 = gcd(G, a_h, b_h).

It suffices to evaluate the four coefficients modulo T.
Exactly the prime factors of G pass the both-killed-by-3
test. Exactly its prime factors dividing G0 also have
both h branches O. If needed the residual support after
removing such primes can be kept by the factor-free
saturation G/gcd(G,G0^k), with k=bit_length(G).
This removes every full power over the unwanted support.

## Actual whole-resultant arithmetic

The checker takes the exact frozen T input hash
1f7305f23e734423b129af730dad0469c224146acacd2c4ea50e065c7493bc16.
It evaluates the normalized division recurrences in the
quadratic ring (Z/T Z)[s]/(s²−2), without inversions or
evaluation of either elliptic point. The canonical
literal index 3h has only 81 bits. Memoized relative
indices suffice even though T has above ten thousand
bits. From the actual results,

| T | both killed by 3, G | both h O, G0 | saturated support |
|---|---:|---:|---:|
| H | 546769 | 546769 | 1 |
| L' | 1384969 | 1384969 | 1 |

Every literal prime on the moving H or L' side of this
locus therefore fails the nonzero-order-three condition.
The partial factor screen is no longer needed for the
exclusion, and unresolved cofactors of the old eliminants
are no longer an arithmetic gap **for this specific
locus**. At other p where the indexed h point has higher
order, one of the two labels is not killed by 3, or where
the bare order-three eliminant does not apply, this gives
no new local sign test.

In particular it supplies neither a genuine k0-negative
L' prime nor an eligible new H divisor. No normalized τ,
positive third Selmer class, numeric denominator phase,
or rational point follows. The replay took about 6.5 s.
