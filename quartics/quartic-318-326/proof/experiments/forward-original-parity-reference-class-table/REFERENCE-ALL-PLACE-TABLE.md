# The eight literal reference squareclasses

This is the finite signed-class completion for the original
$E_n:y^2=x(x-n)(x+3n)$ at $n=11,23$. No rational rank or parity is assumed.
The two files are staged source; no Lean or hosted check ran.

## Exact four filters

The Kummer ordering is $(x+3n,x-n)$ with adjusted root coordinates. The
rational torsion images at $(n,0)$ and $(-3n,0)$ are $(n,1)$ and $(3,-n)$
respectively. The good-place valuation test limits both coordinates to signed
squarefree labels in the primes $2,3,n$, giving $16^2=256$ pairs. For an
integral nonroot point at a good odd prime at most one of the three root
differences is nonunit, so its valuation is even by the cubic. With
nonintegral $x$ the three valuations agree and again are even. At roots the
adjusted factors are units.

| Place | Exact filter in the stated coordinates | Survivors, either reference |
| --- | --- | ---: |
| Real | First sign positive, second sign arbitrary | 128 |
| 3 | Second class is a square: its valuation bit is zero and its stripped unit is 1 mod 3 | 32 |
| $n$ | First stripped unit is a square mod $n$; multiplying the second stripped unit by $(-1)^{v_n B}$ gives a square mod $n$ | 16 |
| 2 | Both valuation bits zero; all four first odd units allowed and second odd unit is 1 or 5 mod 8 | 8 |

At an odd local place the group modulo doubles has size 4, and at the dyadic
place it has size 8. This follows from the exact multiplication-by-2 sequence
for a sufficiently small open formal-logarithm subgroup: it is isomorphic to
$\mathbb Z_p$ additively, and the finite quotient cancels kernel against
cokernel. Thus $[E_n(\mathbb Q_p):2E_n(\mathbb Q_p)]
=\#E_n(\mathbb Q_p)[2]\,[\mathbb Z_p:2\mathbb Z_p]$.
At 3 the torsion supplies independent first classes $n$ (nonsquare unit)
and 3 (odd valuation), and $-n$ is square. At $n$, the torsion valuation
bits are independent, and 3 is a square. At infinity the two real sign
classes follow from the real components and are both attained by torsion.
At 2 the torsion images plus the following affine point classes attain the
whole claimed local group:

- $n=11$, $x=-76$: the cubic is $4(-71079)$ with odd part $1\bmod8$,
  so there is a local ordinate. Kummer coordinates $(-43,-87)$ have
  odd unit residues $(5,1)$ and even valuations. The torsion first-unit set
  before adjoining this class is $\{1,3\}$.
- $n=23$, $x=-85$: the cubic is $64(-2295)$ with odd part $1\bmod8$.
  Kummer coordinates $(-16,-108)$ have odd unit residues $(7,5)$ and
  even valuations. The torsion second unit was always 1.

Consequently the same surviving labels at both references are
$\{1,3,n,3n\}\times\{1,-n\}$. They also occur globally: the previous
`OriginalParityReferencePoints318.reference_class_all_places` supplies the
$(3,1)$ class from actual rational points, alongside the two actual rational
torsion images. This gives all eight without a rational rank hypothesis.
The good-place lower bound needs no separate local model because the
witnesses are rational.

## What the two source leaves supply

- `OriginalParityReferenceClassTable318` is the Mathlib-only fallback.
  `square_residues11` and `square_residues23` check the exact unit lists.
  `initial_counts`, `counts11`, `counts23`, `final11`, and `final23`
  prove stage counts and equality of the final finite predicates, on literal
  sign/prime bits. The ring action and the local image exactness argument
  above are not asserted as native in this table.
- `OriginalParityReferenceActualUpper318.adelic_shapes` instead consumes
  the actual local-witness structure `ActualTwoDescentAdelicPairData318.AdelicPair`.
  `actual_adelic_pair_of_all_places` converts an actual pair in
  `allPlacesImage` into exactly this witness structure, including real sign
  and genuine finite-place square multipliers. The source reuses
  `actual_adelic_normalization` for support (which has already imposed
  dyadic valuation parity, the 3-adic second valuation, and real sign);
  then `actual_signed_local_normalization` at 3 and
  `actual_represented_three` force the remaining second sign to match
  its $n$-exponent. Thus it produces literal representatives, with actual
  nonzero rational square factors, of the same eight classes. The
  redundant support-prime and dyadic unit refinements from the full table do
  not need to be reproved for this upper-bound route.

A wrapper turning these shapes into `Nat.card (allPlacesImage …) = 8`,
or identifying the count with the genuine cohomological Selmer group, is
not claimed by these files. Their scope also excludes reference root signs,
selected corank, and rational rank.
