# At the original scalar index, an exact shift choice eliminates every exceptional denominator sign

This is a **different scalar specialization**, not an evaluation of the old fixed one.
Keep input a=0, the original real index h=473592745039516333133760, source point
P=(1+√2,2√2) on y²=x³−(3−√2)²x, the same original two positive constants
R=4376874610839020 and β=204618888056724185, and the original anchor setting
K=6¹⁵3⁶⁵⁵³⁶. Keep precisely the original label and folded scalar formulas
s=1+i, i=KJ, c=12W/M, M=1+2448β, W=N²+RQ², where
N=Norm(1+U_h²/R) and Q=Norm(U_i)/(Norm(U_h)R¹⁵).
Replace only the permitted positive J by TJ, with T defined below without
materializing it. In particular this uses a literal scalar source at a
permitted index and not a separately given Ready numerical example.
It does not preserve the entire squareclass θ, give a simultaneous four-pole
detector construction, or supply a rational PointPair.

## 1. Bound the primes which could be on the h side of a crossing

Use projective Kummer coordinates [X:Z] for x, in Z[√2]. Let
D=(3−√2)². The exact doubling pair and the differential-addition pair
with fixed difference P are

    doub(X,Z) = ((X²+D Z²)², 4XZ(X²−D Z²)),
    add((X,Z),(Y,V)) = ((XY+D ZV)²,(1+√2)(XV−ZY)²).

The second formula is the product identity for x(P₁+P₂)x(P₁−P₂) on
y²=x³−Dx, with x(P₁−P₂)=x(P). The polynomial formulas hold
also at infinity, away from their base points. On the adjacent multiples
[n]P,[n+1]P there is no base point over Q(√2):
if both finite, equality of x would mean equal points or opposite points.
The first would give P=O; the second would give (2n+1)P=O.
The source point is nontorsion. When exactly one is infinity the other
is ±P, with nonzero x; the displayed pair works directly. For doub the
two coordinates never vanish together over Q(√2) because D≠0 and
characteristic zero. Thus an unreduced homogeneous binary ladder for [2h]P
is exact; no gcd or height estimate for reduced points is used.

Put ‖a+b√2‖=|a|+2|b|, which is submultiplicative. The four coordinates
in an adjacent pair start bounded by 3 for O,P. Each bit replaces a bound
A≥1 by at most 576 A⁴: ‖D‖=23, ‖x(P)‖=3, and the respective constants
are (1+23)², 4(1+23), and 4·3 for the other coordinate bounds.
Writing L=bitlen(2h)=80 and starting with 2² gives
log₂ A≤(2+10/3)4ᴸ−10/3<6·4ᴸ.
Because |Norm(X)|≤‖X‖², for the final numerator

    0 < |Norm(X_[2h]P)| ≤ 2ᴴ,   H = 12·4ᴸ.

Its numerator is nonzero since [2h]P is not finite 2-torsion.
If U_h is a pole at any good place over p, then the exact
x([2h]P)=1/U_h² has positive depth. Even if the ladder coordinates
have common reduction zero, v(X)>v(Z)≥0, so p divides that numerator
norm. In particular every such p is at most 2ᴴ.

Now choose v₂(iT)≥H+2. At a good split rational p≤2ᴴ, if U_[iT]
had a pole then [iT]P would have exact residue order 4.
The residue order of P would be divisible by 2^(v₂(iT)+2),
which is larger than 2p+1, the elementary bound obtained by counting
at most two y values at each affine x and adding infinity. Contradiction.
At inert good primes there is no possible negative odd denominator:
the two charts are integral by the known inert 2-primary order bound
≤5, since 64 divides both indices.

At a remaining good odd p outside 2·3·7·R·M,
the actual W has negative odd depth only if the two norm terms have
equal negative depth before squaring. Hence U_h has a pole. The
known crossing argument then forces an opposite-arm U_[iT] pole:
on an h-pole arm the even multiple sends the doubled torsion point to
the formal group, giving positive chart depth; on any h-zero arm the
new depth is at least the old one by formal multiplication.
If both h charts were poles, or the other were a zero, the Q term
could not match. Otherwise the other h chart is a unit, and the
remaining negative Q depth requires a pole there. The argument
also permits p dividing T or i/h since multiplication adds, rather
than subtracts, formal depth. The bound above excludes the crossing
altogether. Thus every extra odd denominator prime disappears.

## 2. Preserve the fixed rows with an explicit compact T

For each of the following sites use the displayed modulus for the
translated index. The older exact local replays supply nonzero
chart denominators at the affine points; their moduli can be checked
by the literal group laws and formal groups:

| p | sufficient modulus for i | required preserved data |
|---:|---:|---|
| 7 | 196 | two chart values mod49, both norms 42 mod49 |
| 181 | 32724 | W=146 mod p |
| 1346909 | 1814161575200 | W=429536 mod p |
| 70850399941 | 5019779171659796018964 | W=66349154550 mod p |
| 6551 | 6551·lcm(1638,364) | δ/p=684 mod p |
| 2470991 | 2470991·lcm(51479,308874) | δ/p=2223081 mod p |
| 16782959 | 16782959·lcm(2097870,699290) | δ/p=13715188 mod p |

At 7 the two source orders in the nonsingular locus are 7 and 4
(the first is in the bad minimal cusp chart). Multiplication by
7 once more gives depth two in its formal kernel. Thus preservation
of i modulo 196 preserves the computed charts mod49. Cancelling the
single 7 in the two source norms gives the same W=5 mod7 and c=1 mod7.
At the three inert normalizer primes the displayed integers annihilate
the residue point, and regular charts and unit h norm give the same W
mod p. The three additional θ primes are split; their displayed
orders put the difference in the formal kernel modulo p². Their
h chart norms are units, so the entire old c mod p² is retained,
not just its residue.

At 29 both source points are formal at both old indices in the
single unramified quadratic completion. The exact residue check
uses an annihilator 800 to reduce the two indices and checks their
resulting points are both O. The old W has valuation zero: N≡1 mod29,
v(Q)=2v₂₉(i/h)≥0, and −R is nonsquare there. The same proof gives
valuation zero after multiplying by integral T. Thus c has its fixed
depth −1 at all four primes of M.
At 131 the original h chart is depth ≥2 and the old divisibility on
i/h yields W≡1 mod131². This divisibility survives. The other original
small-place W unit and local Ready square/depth constraints survive
as above, since h is not changed and i/h only acquires integral
factors. In particular the only sign possibilities at 2,3,17 and
the eight β places are the same as before. The literal source real
margin depends only on h and is unchanged. The new labels from
s=1+K(TJ) are still positive odd admissible labels. Modulo the
guard prime 5 the unchanged h is formal, s≡1 and the Lucas labels
reduce to the same (3723,1,−1,1); the same four nonzero guard rows
work. The scalar domain and square denominator follow from the
unchanged source domain and local unit criterion.

For explicitness, let C be the least common multiple of all **odd
parts** of the seven periods in the table. Their 2-parts all divide
2²², which divides old i. Take

    B = H+2,
    r = the least positive residue of (2^B)^(−1) modulo C,
    T = 2^B r.

The seven index congruences follow since T≡1 mod C, independently of
the high 2-adic part. This defines one positive integer J*=TJ with a
short exponent expression (B has 164 bits), not with an evaluated
large integer or expanded coordinates. Modular exponentiation only
uses the 164 exponent bits. No optimization in B is claimed.

Therefore the **entire odd denominator squareclass of the retuned c**
is the known M=29·181·1346909·70850399941. At all other odd places
no pole or only even depth survives. This is not a statement about
the raw denominator or its even components. In particular the retuned
D_exc is 1.

## 3. What this does to the constant-15 conditional rank test

Let δ*=1−β(c*)² and θ*=[δ*] for this retuned actual scalar (the star
denotes the new specialization here). The four known primes all still
occur with odd depth, their stripped-unit signs at the known primes
are the same, and θ* is square at the old β places, 2 and 3.
We do not infer any roster of other primes. It has at least one
other prime by its 2-adic square class and the mod-8 product of the
four visible primes.

**If exactly one prime is hidden**, the same aggregate character
row determines the same two 4-element scalar Selmer spaces
up to replacing θ,d by θ*,βθ*. In particular e=2952271997968816765
is admitted to the opposite scalar test and θ* is a √5 norm.
The named second cross pairing of the previous conductor-15 formula
is now certainly −1 because D_exc=1. The previously evaluated four
normalizer Jacobi signs have product +1 and the visible θ-local sign
has product −1. No crossed-character premise is needed for this
retuned branch.

To state the precise rank consequence, Fisher's
[Higher descents, Theorem 2.1](https://www.dpmms.cam.ac.uk/~taf1000/papers/higherdesc.pdf)
identifies both kernels of the cross form with the two third descent
images. At 4/4 both first forms are zero. The single −1 shows that
both third images are exactly the torsion lines, so both rational
scalar images also have dimension one. The dual-isogeny rank
identity gives rank zero. The same exact sequences identify each [2]
of Sha with an extension of two one-dimensional F₂ spaces, so each
has order four. There is no order-four class: for z in Sha(E)[4],
φz lies in Sha(E′)[2ψ]. Its double lies in the zero opposite third
Sha image, so [2]φz=0. Hence z lies in Sha(E)[2φ], and [2]z lies
in the zero third Sha image on E. Swap φ and ψ for the other curve. Thus in this
conditional branch the two primary Sha groups are exactly (Z/2)²,
with no finiteness assumption. The argument also applies to the
old scalar **if** both its one-hidden count and crossed sign + are
independently supplied.

This gives a certified denominator control in the exact allowed
retuned scalar. It does not prove the one-hidden hypothesis,
decide the initial scalar, or obstruct other PointPair receivers.
It gives no rational point or ranks on the full four-pole system.

    sha256sum -c SHA256SUMS
    python3 -B check_retune.py | cmp - EXACT-RETUNE-CONTROLS.json
