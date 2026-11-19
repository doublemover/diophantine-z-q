# The existing fixed 181-variable quartic at N=15

**Claim and scope.** For the specific integer polynomial `quartic181-N15.txt`
(SHA-256 4550b1785b53333f6f922409bc3c197c947b702fc16162468d602a63031284c1),
under exactly the effective arithmetic suppliers of the independently reviewed fixed182
donor, its projection on the first rational coordinate is Z. There are 180
existentially quantified rational witnesses in addition to this input. Neither
this proof nor its verifiers prove the underlying height/modularity, group, pole
or prime-pattern suppliers in Lean. The fixed180 and the exact 167/165 are separate polynomials.

**Exact inverse comparison.** The adjacent `check.py` uses only rational algebra,
SymPy and the frozen candidate and donor files. It undoes the nonzero rational
149-diagonal (input fixed), the integer q-weights (input weight zero), and the
harmonic elimination of u₂=q+3−u₀−u₁. Before that substitution it checks the
literal inverse guard (u₀+u₁+u₂−3)w=1 after undoing the constant diagonal.
Therefore the coordinate comparison works in both directions on the whole
rational locus, not a Zariski-open slice imposed on the input. Exactly 149
residuals including the guard agree with the reviewed donor in order up to
individually nonzero rational Laurent monomials. In particular the three measured
arguments, both signed aggregate coefficients, all eight mixed factors, true four
points, signed β input, independent fourth pole and three harmonic cap/pole
pairs are those of the donor. Five other donor rows are replaced by four scalar
rows. The quartic is their sum of squares over Q, so every rational zero satisfies
all 153 residuals. Direct expansion gives 3,338 monomials, degree four,
307-bit maximal coefficient, coefficient 1 at X⁴, 92,690 plain-text bytes.
The old transfer metadata field `a` accidentally stores a stringified solver
return, not the interpolation center; it is neither executed nor trusted.
The actual inverse row gives the center below. The old four output files are unaltered.

**Scalar identity and guards.** Set C=149¹⁵, ℓ=557·149²,
s=X², β=1−51s, P(B)=B(B−2401)(32B+343), b₀=705024, A=P(b₀),
a₀=(1−b₀)/51=−705023/51. The inverse row gives v=1/(s−a₀),
globally defined on Q. The denominator row after substitution is equivalent to
(P(β)−A)R=(ℓ/149)C²P(β). At 149, scanning X mod 149 shows both
P(β),P(β)−A are units if X is integral there. If not,
v₁₄₉P=6v₁₄₉X<0=v₁₄₉A, and v₁₄₉(P−A)=v₁₄₉P. Thus on *all*
rational inputs R is finite/nonzero and m₁₄₉=v₁₄₉R=31.
Physical rows after the exact undoing read x111²=x105 x113 and
x64²−8x65²+x110²+q x109−C x111 x112=0; R=C x113/q,
x112=C x113²/q. Under the same scalar-ratio readout as the donor they give
b=R³W², W=Z₀⁴/R¹⁰+Z₁²/R⁷+F²/R⁴, not the previous pole.
Here Z=2z(Q₂)/z(H) and F is the rational norm of the reciprocal of x(H).
No change was made to scalar conic realizability, and no extraction of a
rational square root of R is required.

**Reverse.** At 149 the raw reference reciprocal cannot vanish:
if its two components zero, its two stored square terms vanish and the retained
first reference pair forces x150=87/41, x151=−129/164 in the q-normalized
chart; the next two residuals reduce to −1714299/164 and −42776519/164.
At a good scalar prime of odd positive depth m the finite valuations in W have
classes 2 mod 4, odd, 0 mod 4, since vₚ(F) is even for the actual reference.
Zero summands are omitted; F≠0. Thus W≠0, vₚ(b)=3m+2vₚ(W) is odd,
and the original pole forbids negative odd valuation. Accordingly vₚ(Z₀)>17m/8,
vₚ(Z₁)>11m/4, vₚ(F)>5m/4. First apply this with m=31 at 149 to the
raw scalar entries: the same forbidden finite reference torsion and shifted
strata of the donor have 149-unit reciprocal norm, so these are excluded
*before* logarithm division. The unchanged true-point charts (not an inverse
for the unused alternate scalar ratio) give h nonzero and not one and a nonzero
scalar index a. At some place over each consumed p the reference is formal and
Q₂ is formal up to the permitted 2-torsion translate. The unchanged unramified
formal logarithm and integral h give vₚ(a)>17m/8. This yields p³ for m≥1;
at 149 it yields 149⁶⁶ since 17·31/8=65+7/8.

X=0 is already integral. For X≠0, β≠1 and the 149 scan excludes the other
three finite height contacts. Use Brox v62 H4.1 on its original radical M_S(β),
S={2,3,5,7,11,13,17,37,41,2399}; do *not* enlarge this theorem's S.
Outside S, both negative vₚ(β) and finite vₚ(β−1) for integral β are even.
At 149 the other finite contacts are avoided and it never contributes to
M_S. Factor A=2⁹3⁴·17·41·43·67·191·702623. Discard at most
D=43·67·191·557·702623=215354614883981 from the squarefree M_S,
only on the scalar side; D includes the new numerator prime 557. Write
M'=M_S/gcd(M_S,D). At each p|M' a unique factor of P has positive odd
order, P−A is a unit, and vₚ(R)=vₚ(P)=m. Thus 149⁶⁶ (M')³ divides c=|a|.
The original numerical H4.1 consequence h(β)<2²³⁸ M_S³ gives
h(β)<2²³⁸D³149⁻⁶⁶c<c/2 (checked as an integer inequality).
The three generic and exceptional harmonic charts, successful signed marks
and two-component height calculation keep the exact old comparison set
Γ=S∪{79,89,647,3593}; no comparison radical loses 557 or any factor of A.
The unchanged quantitative v62 Δ≠0 contradiction needs c≥149⁶⁶; in Δ=0
Lucas gives log B>320c, whereas J_X≠0 would give log B<240+c.
Hence J_X=0, β=n∈½Z, and in X=u/d reduced we have d²|102. The latter
is squarefree, so X∈Z.

**Forward, including zero.** For every integer X, including zero,
P(β)≤−900000 (strictly more negative for |X|≥1 by each absolute factor).
Since A>0, R≥(ℓ/149)C²·900000/(A+900000)>2²⁰. The existing compact real
preparation |Z_i|<2¹², 0<|F|≤1/7 gives W>0 and b<2¹⁰⁰/R⁵<17.
For integer X the exact possibilities for v₂P are {1,2,4,5}, v₃P=2 and
v₁₇P=0. Thus A/P has valuation ≥3,1,1 respectively. The unit 1−A/P
is a local square there, as is ℓ/149=557·149 since 557≡149 mod 8,3,17.
So each R is a nonzero local square at all three. Fix this R. At **every**
prime with odd vₚR, positive or negative, choose the actual reference
and then the scalar point in the existing allowable progressions, arbitrarily
deep above those finitely many primes as needed so each W-summand has
valuation ≥max(0,ceil(−3vₚ(R)/2)). Also prescribe sufficiently deep W at
2,3,17 for the scalar pole thresholds. The scalar input b then has square
reduced denominator: others have even vₚ(b), irrespective of W; each odd
support prime has nonnegative valuation. The rational W is nonzero by the
real bound. Thus the genuine scalar pole is prepared at N=15, rather than
borrowing a witness for a different b. The final reference return is taken
in these same open neighborhoods. No bound on their size uniform in X is used.
The true Q₁=[β]P₀ is a non-torsion double whether β is negative or (at X=0)
equal to 1; negative indices are allowed. All finite exceptional offsets,
multipliers and support just fixed are excluded before the thirty primes.

The three complete comparison assemblies and actual point sums match fixed182
literally after the invertible chart. Their integer construction uses 30 distinct
translated marks, separation ≥7,≥9, and the existing split primes with the
arbitrarily large real slope, cutoff and prescribed denominators. It can impose
pmax≤5pmin/4 with pmin>76176. The Hasse bound and full rational 2-torsion
exclude selected primes from the retained reduction orders, giving the
ordinary simultaneous signed equal-depth CRT. At each selected prime u_j has
valuation −1 on its mark, the others are integral and q/u_j≡1 there; at the
targeted finite places all u_j→1, and at real infinity they approach 1 from
above. Thus q=u₀+u₁+u₂−3 is nonzero, mixed successful factors yield
Ntr a unit, comparison b_j has order one at its marks and square reduced
denominator, and all three actual square/real preparations go through. This
uses the fixed182 supplier, not a new independent 30-prime assertion. It
produces a rational zero over each integer without requiring every old 182
witness to lift; the scalar witness changes.

Sources: José Brox v62/v74 and their declared suppliers as in the sealed
182 packet (CC BY 4.0); cited fixed182 README/BASE188/BASE184 and preceding
centered scalar, and the independent cubic-pole review 9f073834… (whose own
two-comparison chart had no N=15 conclusion). This audit is of a previously
generated specialized literal only; it is neither a Git release nor a formal
kernel acceptance.
