# The three existing local contacts force nine previously unhit support classes

Use the exact original three scales of the frozen triad and six-incidence
certificates. Stay on the square branch t=(r/d)^2, d=B^N, N≥2, r coprime
to B, with real T_j=c_j²t larger than every root. Here B is exactly the
collision saturation integer of the three-scale prime router. Distinguish
the twelve nonzero scaled root classes s_{ji}=θ_i/c_j²; they are already
separated by the triad's modular arithmetic. Write σ_{ji} for the positive
squarefree class of c_j²t−θ_i. Its odd support lies outside B and cannot
be shared by a different root class. This uses the router for odd support,
not an assumption that the published contact roster is complete.

## Pointwise row and residual cofactor

At a specified contact prime p of class a=(j,2), where θ_2=−1, each
other class b=(k,i) has c_k²t−θ_i a p-unit. Thus

    (σ_b/p) = ( (c_k²t−θ_i) mod p / p ).

The right side is available before any factorization from the fixed
c_k and r/d modulo p² in the exact triad/six records. If it is negative,
σ_b is not 1 and its support is nonempty. The zero root is not a column:
on this branch c_k²t is a global square.

For the diagonal p∈σ_a, all these contacts have c_j²t+1=p mod p²,
so ((σ_a/p)/p)=+1, where the inner σ_a/p is the integer quotient and
the outer /p is the Legendre symbol. Indeed in the equality
c_j²t+1=σ_a u², the rational u is a p-unit (both valuations are one),
and (c_j²t+1)/p≡1 mod p. In either case let K_b be the product of the
known members of σ_b and X_b=σ_b/K_b the still unknown squarefree
cofactor. Divide the known product K_b (omitting p first if this is
the diagonal class); this gives the explicit symbol (X_b/p).
The replay records these rows too, not merely the nonempty witnesses.
A proposed full support must reproduce every row, including the
diagonal stripped units. This is a necessary finite linear signature
test on a proposed support, never a factorization or sufficiency test.

## Nine explicit unhit columns (already from the triad)

The row indices 0,1,2 denote slots 190,241,292. Indices 1,3,4
denote roots −1/2,1/2399,−32/407. In each cell below the indicated
named triad prime gives a nonsquare:

| Row | θ_1 | θ_3 | θ_4 |
| --- | ---: | ---: | ---: |
| 0 | 3641809 | 3641809 | 3641809 |
| 1 | 4247281 | 3162001 | 3162001 |
| 2 | 3162001 | 3162001 | 3162001 |

The same prime can give more than one negative **test**, but the
forced new actual prime supports are in nine different root classes,
and hence are pairwise disjoint and disjoint from all known θ_2
contacts. In addition, each θ_2 class still needs an extra prime:
in the triad separately at 7, and in the six residue system
respectively at 23,19,19. This is the prior local-square character
condition at a prime dividing B. Those three extra primes are in
three other, distinct classes; there is no double counting.

Accordingly every completion on this exact saturated square branch
that preserves the three named residue contacts has at least **15**
odd-support primes (3 known + 3 forced in their own classes + 9 in
unhit classes). Preserving all six named contacts sharpens this to
**18** (6 + 3 + 9). The witnesses in the table are certification data,
not names of any of those unseen primes.

## Aggregate pairing check for any fully proposed two classes

For different classes a,b and any p|σ_a, evaluate the unit of b at
the root of a: (σ_b/p)=((s_a−s_b)/p), since c_k² is a unit square.
All prime factors in the numerator and denominator of the nonzero
rational difference s_a−s_b divide B by the cross determinant.
Taking the product over p|σ_a and applying quadratic reciprocity
gives the Jacobi symbol (σ_b/σ_a)=+1: the factors −1 and 2 give
+ because σ_a≡1 mod8, and every odd l|B gives
(l/σ_a)=(σ_a/l)=+ by the independent saturation character condition.
This aggregate symmetry does not imply the individual pointwise
rows or locate any new prime; it is a necessary consistency check
on any fully proposed support.

Run:
    python3 -B check_actual_cross_support.py | cmp - EXACT-CROSS-SYMBOL-ROWS.json
    sha256sum -c SHA256SUMS

The checker consumes the byte-pinned prior triad and six JSONs from
sibling directories. It does not find any new odd-support prime,
enumerate other charts, prove square pole denominators, or build Lean.
