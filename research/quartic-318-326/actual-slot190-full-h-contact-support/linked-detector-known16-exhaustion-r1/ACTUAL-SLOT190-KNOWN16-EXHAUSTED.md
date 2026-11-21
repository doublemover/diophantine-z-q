# Every square-t witness at this fixed h needs an odd contact prime beyond the known 16

Use the literal unscaled slot190 at the fixed retuned h,J and
explicit labels of a7dd144b…. Let t=(R/D)²>2 in lowest terms,
with R,D>0, v₂(D)≥2 and 3·17|D. These are weaker small-place
depth assumptions than the constructive prefix. The existing
fixed-h contact lemma applies with its finite exceptional set S.
This proof concerns the square-t chart, not arbitrary t or h.

Let U be the exact sixteen nominated primes

    5,7,11,13,37,53,109,131,163,439,661,733,1489,1861,2399,1041427.

**If slot190 has a PointPair, some odd prime p∉U has odd positive
valuation in a contact numerator below.** Such a p belongs to
the actual coefficient-exceptional set S, and p∤D. Thus this
chart requires a new actual contribution outside the known
support, not a different saturation choice within it.

## Forced classes at 2,3,17,5 and 7

Write G_i=a_i R²+b_i D² with
(a_i,b_i)=(2,1),(1,1),(2399,−1),(407,32); G_0=R² contributes
nothing. All four G_i are positive since t>2. Suppose no odd
positive exponent occurs at an odd prime outside U. Set
γ_i=sf(G_i)>0. At 2 the valuations are exactly those of a_i.
The ratio G_i/a_i=R²+(b_i/a_i)D² is a square unit at 2
after this exact normalization, at 3, and at 17. It follows
that the odd parts of γ_i and a_i have the same residue
modulo 24 and the same Legendre symbol at 17.

If p∈U divides D, then v_p(G_i)=v_p(a_i), since the a_i are
squarefree and 2v_p(D)>v_p(a_i). At a free p (meaning p∤D),
a possible odd contribution to γ_i requires p∤a_i and
(−a_i b_i/p)=+1. If p|a_i and p∤D, the corresponding b_i
is a unit, so p is removed from the baseline. Thus the
baseline depends on which of 11,37,2399 divide D. The
other saturation statuses may be relaxed to free because
they only remove possible moving primes, not the baseline.

At 5, first take D a unit. The exact earlier admissible
first-form enumeration d9c7db93… gives γ_1=2d with d one
of 1,1441,169752601,244613498041, all 1 mod5. The same
list is a superset if any earlier candidate primes now
divide D. So γ_1 is nonsquare mod5. For square
T=R²/D² mod5, G_1/D²=2T+1 is nonsquare only at T=1,
not at T=0 or 4. This fixes all four unit symbols at 5
to (−,−,−,+). If 5 divides D, the symbols are (−,+,+,−)
from the leading terms. In both cases 5 cannot appear
in any γ_i. At 7 no a_iT+b_i vanishes at a square T
when D is a unit (all their roots are nonsquares), and
a_i is a unit if 7 divides D. So 7 never appears either.

## Complete finite enumeration at the remaining places

The only special saturation statuses are the four bits
5|D, 11|D, 37|D, 2399|D. Enumerate all 16 possibilities.
All other statuses may be relaxed to free: an ordinary
prime dividing D simply cannot be chosen in a mask.

For i≠j, the exact determinants ∆_ij=a_i b_j−a_j b_i
are units at the remaining possible moving primes (all
determinant support is in {2,3,5,7}). Thus distinct
moving masks are disjoint. At p in the mask of i, D
is a unit, and the literal root gives

    G_j/D² ≡ ∆_ij/a_i (mod p),
    (γ_j/p) = (∆_ij a_i/p).

The replay takes each γ_i as its saturation baseline times
an eligible subset, retains the normalized 24/17 and 5
signs, and checks the determinant signs in both directions.
There are **no surviving rows in 15 cases**. When all
four special primes divide D, the only remaining row is

    (γ_1,γ_2,γ_3,γ_4) = (2,1,2399,407).

The cold-checked rank-zero congruent-number E₂ computation
(a6082bf3…) excludes even this row: G_1/2 and G_2 squares
would give a nondegenerate right triangle of area 2. This
is unconditional, not a bounded rational-point scan.

The assumed absence of a new odd support prime is therefore
impossible. For an actual PointPair that prime must belong
to S by the checked odd contact valuation obstruction, and
cannot divide D because the entire leading-coefficient
support is in U∪{2}. Leaving an irrelevant exceptional
prime outside D is not enough: it must occur at odd depth
in a contact numerator. No such prime or point is produced
here; other actual exceptional support, nonsquare t and
the original mixed-CRT ordering remain open.

The adjacent code lists the literal class masks and join
counts rather than using a rank oracle. It requires no
expanded h-coordinates, factorization of S, prime-pattern
theorem, or Lean job.

```sh
python3 -B check_fixed_h_known16.py | cmp - EXACT-KNOWN16-EXHAUSTION.json
sha256sum -c SHA256SUMS
```
