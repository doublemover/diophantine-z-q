# Original Gaussian Weber conductor: the short positive branch

## One recommended native theorem

**`ActualGaussianWeberPrimitivePointNorm318.norm_one_of_fixed_primitive_value`**
is the smallest scoped source to test that reaches the actual primitive
norm implication. The exact eight-module selector contains four strictly
green sources (three PointMap files and QuarterTurn from job 137063283077),
three prior source-only bodies unchanged, and one new proof. There is no
number-field, analytic, uniformization or legacy wrapper dependency. The
six-module orbit-only selector is for localization, not another proposed
run. This packet is source-only.

Use the actual stock points of E: y² = x³ − x, the chosen quarter-turn
J(x,y) = (−x,iy), and the option-valued Weber coordinate ω(P) = x(P)²
with ω(O) = none. The only part of primitivity needed is the implication

    [c]P + [d]JP = O  ==>  M | c and M | d

for every pair of integers c,d. If M is even, a² + b² = p and
ω([a]P + [b]JP) = ω(P), then 2M divides p − 1.

Indeed, equal squared abscissae give u = x or u = −x. The literal cubic
then gives v = ±y or v = ±iy, respectively. Infinity is a separate
fibre; coincidence between unit turns causes no problem. Subtract the
matching unit pair (c,d) from (a,b), obtaining a − c = Mx and b − d = My.
The difference from the unit's norm is 2M(cx + dy) + M²(x² + y²), a
multiple of 2M since M is even and c² + d² = 1. The checked finite
controls use the point law on this actual curve, including repeated turns.

The existing legacy `Coordinates L h2 M` and `primitive L h2 C` supply
this separation on the same point P. Apply `C.linear` with coordinate
`C.equiv P = 1` and compare against `C.linear 0 0 P` for the zero point.
A scalar killing P gives equal quotient classes of the literal pairs
(c,d) and (0,0). `ActualGaussianResidueOrbit318.full_coordinate_congruence`
for this same quotient ideal gives the two divisibilities (negate a
witness if needed). This adapter is the precise typed next consumer,
not part of the eight-module statement.

## The signed CM path

1. **Actual arithmetic place.** Use the one prime w of the full torsion
   field over the specified original Weber prime v. For the chosen
   degree-one Gaussian ideal with generator π = a + bi of norm p > 6,
   the residue root is `rootOf a b` = −a/b in the actual prime field,
   not the conjugate root. ChosenPlace3r3, IntegerGalois5r5,
   RingFrob6r2 and LocalFrob7r4 provide the literal prime, tower,
   automorphism and p-power on the whole chosen residue field.
   PointFrob12r4 covers every stock point, including infinity.
   Torsion16r2 gives additive reduction and injectivity on M-torsion
   for p not dividing M. None of these asserts a CM scalar formula.
2. **Actual unsigned generic branch.** Odd-norm translation by (0,0)
   commutes with [π], which fixes (0,0); it excludes generic infinity.
   Negation puts the same generic scalar's abscissa in k(X) and
   ordinate in Yk(X). The same positive-I complex uniformization,
   fixed before choosing p, supplies p points per fibre of this scalar
   on the original complex curve. A generic abscissa fibre, pairing
   the opposite ordinates, bounds the degree of this very rational
   abscissa by p. Normalize its numerator and denominator primitively
   in the chosen Gauss valuation: the reduced denominator survives
   and degree cannot rise. The origin jet vanishes since
   a + b rootOf(a,b) = 0 in the chosen residue. Translated by the
   literal mixed chord, this forces the rational abscissa derivative
   to vanish. The real pole at O, the cap and coprimeness yield
   x = A Xᵖ + B. The three branch roots and the odd ordinate equation
   give A = ±1, B = 0 and the matching two signs of Yᵖ or iYᵖ.
   `ResidualDegreeGate318` (47 closure) exposes this four-way finite
   generic comparison conditional on the same capped presentation.
   Complex same-map fibre and capped-presentation suppliers remain
   real prerequisites. This is not a hosted theorem.
3. **Positive normalization for the full action.** Choose the unique
   primary associate π − 1 = (1 + i)³(c + di), exactly
   a = 1 − 2(c + d), b = 2(c − d). The point Q = (i,1 − i) is
   rational over the chosen prime field and satisfies
   [2]Q = [2]JQ = (0,0). Hence the primary pair fixes Q.
   Coordinate comparison excludes the other three unit branches.
   `PrimaryProbe318` (5) checks this elementary calibration but does
   not test the cap, stationarity or primitive norm. Existing
   `FourFrobeniusTurns318` (49), `PrimaryGeneric318` (50) and
   `PrimaryAllPoints318` (52) encode calibration and extension.
   To extend a fixed unit branch, compare the two *additive* maps on
   the very same origin arc and its actual translate, then cancel.
   Handle a residual affine 2-torsion point by translation over the
   auxiliary function field. Equality of squared abscissae is not
   equality of points and is not used for additive cancellation.
4. **Existing lift route.** `ArithmeticTorsionLift318` (31) needs
   only the action on the reduction of its supplied point.
   `ArithmeticFromGeneric318` (65), `FixedNumberFieldTorsion318` (68)
   and `ActualFrobMultiplier318` (86) connect the positive generic
   action to the literal torsion point and the same primitive cyclic
   coordinates. The exact full `ExactUnitKernel318.weber_kernel_exact`
   (79) is an iff for fixing the full Weber field. The positive branch
   can instead read only the chosen primitive value and use this leaf.
5. **Same-place input for the conductor.** Identity of absolute
   arithmetic at the contracted v implies identity of the restriction
   of the relative arithmetic automorphism from w by unramified
   uniqueness at that same v. This implies σ(ω(P)) = ω(P) for the
   actual primitive generator P, not for an arbitrary point with
   unattested value. Once [π]P = σP on the same point, the selected
   leaf gives the exact norm congruence. The existing stock
   `root_mem_of_same_place_norm` may then consume its properly
   quantified same-place condition. The original direct127r2 source
   is untouched and still conditional on positive `PrimaryAbove`.

## A shorter conductor-only route

Step 2 already identifies [π] with ε·Fr for one *fixed* turn ε from
{1, −1, i, −i} on the generic point. The same argument in step 3
extends any fixed turn by additivity, without positive calibration.
At the actual chosen w, compare the two genuine M-torsion points
[π]P and ε·σP through prime-to-p injective reduction. Then
ω([π]P) = ω(ε·σP) = ω(σP) = ω(P), exactly the selected leaf's premise.
The existing source transport uses `Tag.id`; a fixed-tag generalization
is future source, not a claim that the older theorem already takes
arbitrary ε. This shorter branch eliminates a *normalization* and the
*reverse* global kernel implication; the complex cap, actual CM
differential, same-place transport and primitive separation still matter.
It uses neither qualitative class occurrence nor prior cyclotomic
inclusion. It proves no quantitative Frei–Tinková count or rational point.
