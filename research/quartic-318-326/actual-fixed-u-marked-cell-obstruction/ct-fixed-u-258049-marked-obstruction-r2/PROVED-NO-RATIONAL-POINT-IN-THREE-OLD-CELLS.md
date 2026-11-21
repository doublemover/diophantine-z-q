# The exact u=258049 torsor cannot meet three of its old rational contact cells

For the same literal b=10568037907556089 and t=1/2399 as Joined, fix
u=258049 and λ=70946129015908599398441/2130857164832. Consider

    C₂ : W²−t=bY²,     Z²−W²=λ,

mapped to E:y²=x(x−bt)(x+bλ) by (x,y)=(bW²,b²WYZ). Then **there is no
rational point on C₂ with W in the single original ball**

    W ≡ 76392631052750 mod 52056721².

The other two old cells (p,W)=(4818481,5525681088721) and
(16688017,37136702898359) each independently also exclude rational
points. These are three separate failures, not an incompatibility that
requires imposing two or all nineteen balls together. Each one still
has actual points over its own Q_p; the obstruction is to a Q point
approximating it. This result says nothing about unmarked rational rank
or other u/b, and is not the final original pole proof.

## 1. A necessary global affine code, without a Cassels–Tate assumption

Use the three exact integral tangent forms L_i on the same homogeneous
coordinates (Z₀,Z₁,Z₂,H)=(W,bY,Z,1) from the immutable exact C₄ packet.
The forms come from the rational seeds of the three rank-three conic
projections. Their divisors on the genus-one curve are twice the
corresponding degree-two fibers, including over all good odd residue
fields. Thus g₀=L₁L₂/H² and g₁=L₀L₂/H² each have even divisor, whose
half represents the actual T₀=(0,0) and T₁=(bt,0), respectively. The
label follows by deck translation of the original 2-cover: flipping
the two root signs other than i is translation by T_i. Equivalently
one compares the characters of x−e_i, whose half divisor on E is
[T_i]−[O]. This is an identity of the same covers, not a selection
of different representatives.

For a fixed place v, choose any one C₂(Q_v) reference P_v on which
both g_i are nonzero, as in the frozen direct computation. Identifying
C₂(Q_v) with E(Q_v) by translation at P_v, each g_i differs from
x−e_i by a nonzero constant times a rational square, by the two
half-divisor class identities. Principal divisor equivalence descends
to Q_v (Hilbert 90). At a point near the origin, the x−e_i Kummer
constant is square, so the literal `g(P_v)` squareclasses are the
offset. Consequently the possible local pairs are exactly that offset
plus the literal first-two Kummer image of E(Q_v)/2E(Q_v), in the
binary group of local squareclasses. The old exact Sel₂ donor exhibits
all elements of those images, counting 4 at odd bad p, 8 at p=2, and
2 at ∞. At extra odd good small p the Kummer image is the pair of
arbitrary unramified unit classes. There is no assumption of a rational
point on C₂ in deriving these local affine conditions.

Let S be the signed support in the frozen JSON: −1,2,3,5,7,11,13,17,
97,2399,23459,36833,51071,226691,966041,8912209,1185793321,
20555323601,4900372089410977. At an omitted prime the homogeneous
model and each rank-three conic are good; the primitive seeds reduce
to nonzero smooth points, co-normalizations are units, and the
tangent line on the smooth conic is twice its section. Projection
omitting Z_i is a morphism on the smooth model (all three remaining
coordinates cannot vanish even in the fiber), so pulling back the
tangent remains even as a Cartier divisor, with no odd vertical
factor. Hence evaluation at any rational point with g_i defined and
nonzero has even p-valuation; denominator H² contributes only even
valuation. This is why S captures **all** global squareclass pairs,
not just the one explicit C₄ witness or classes chosen by an a priori
height bound.

Now suppose P were a rational C₂ point in one designated ball. The
whole-ball calculation below forces all three L_i nonzero there.
Its pair (g₀(P),g₁(P)) of rational squareclasses, encoded by signed
support S, must obey the exact affine rows at every place in S, since
P itself supplies a rational lift of that twist. Equivalently, it is
one of the 16 total solutions of a rank-34 system with 38 bit variables,
already nonempty. This derivation does not use perfection of a reduced
Sha pairing, Sel₈, or a rational Mordell–Weil generator.

## 2. First cell has a 7-input-row obstruction

At p=52056721, both (W²−t)/b and W²+λ are square p-adic units on the
entire cell. The script computes root lifts at its exact center W
modulo p³, both signs of each root. For any W'≡W mod p², each radicand
retains its residue and the corresponding root of the same sign lies
within p² of the center root (difference-of-squares with unit sum).
Since p∤b, the three Z_i therefore change by multiples of p². The
change in L_i has valuation ≥2 plus the least valuation of its
variable coefficients. At all four signs this is strictly larger
than the displayed actual valuation of L_i, so the root interval
and the entire ball give the same leading units and valuations.
Hence on the whole cell (g₁) is a nonsquare unit class, as is g₀:
the code is 5, where code bits 0 and 2 indicate the unit bits in
(g₀,g₁).

The global condition says (g₁) is a square unit class here (indeed
both coordinates are square for all 16 solutions). A compact
certificate does not need enumerating the 16: XOR the seven **0-based**
raw affine rows numbered 3, 7, 9, 13, 16, 22, 23 in
EXACT-ALPHA-FOUR-COVER.json. The left mask obtained is 61262004224,
the exact global encoding of the g₁ Legendre functional at p=52056721,
and the right bit is 0. The Hensel ball forces bit 1. The literal seven inputs are:

| Row | Place | Mask | RHS |
|---:|---:|---:|---:|
| 3 | 2 | 4888461312 | 1 |
| 7 | 5 | 4194304 | 0 |
| 9 | 7 | 8388608 | 0 |
| 13 | 13 | 33554432 | 0 |
| 16 | 97 | 103997767680 | 0 |
| 22 | 36833 | 99134472192 | 1 |
| 23 | 36833 | 1073741824 | 0 |

 The attached
replay verifies the mask equality, each root congruence and four
margin inequalities, and independently redoes Gaussian elimination.

The other two cells give the additional checks:

| Prime | Center modulo p² | All global codes | All local-ball codes |
|---:|---:|---|---|
| 52056721 | 76392631052750 | {0} | {5} |
| 4818481 | 5525681088721 | {0} | {4} |
| 16688017 | 37136702898359 | {0,5} | {1,4} |

The JSON additionally contains explicit descriptions of the one-row
functional obstruction for each of the last two, not just a search
failure or matching one chosen C₄.

## 3. Consequence and next independent question

Retire this fixed-u candidate for the old marked construction, even
though C₂ is everywhere locally soluble with the old balls, its full
2-Selmer dimension is 4, α lifts to Sel₄, and the exact unmarked C₄ is
itself everywhere locally soluble. These facts are compatible because
no *global* 4-cover twist need realize an arbitrary prescribed open
local component. No claim of unmarked insolubility, failure for all u,
a nonzero higher Cassels–Tate pairing, or rank zero is made. If the
unmarked rank question is pursued, the independent next arithmetic
problem is still the actual T₀ function on that one C₄ and the next
pairing bit. It is no longer needed to reject this marked fixed-u model.

Reproduce both layers from the project workspace:

    C=rc-native-helper-20261120/ct-fixed-u-258049-one-bit-r1
    M=rc-native-helper-20261120/ct-fixed-u-258049-marked-obstruction-r2
    python -B "$C/construct_exact_alpha_four_cover.py" | cmp - "$C/EXACT-ALPHA-FOUR-COVER.json"
    python -B "$M/replay_marked_lift_obstruction.py" | cmp - "$M/EXACT-THREE-SINGLE-CELL-OBSTRUCTIONS.json"

Both are exact bounded integer/rational checks, no Lean/build/push.
This r2 restores the three displayed center Z roots, which r1’s local XOR
accumulator shadowed at JSON serialization only. All sign evaluations,
Hensel bounds, obstruction rows and mathematical claims are unchanged.
