# Genuine period parameter across exceptional j values

Status: frozen source packet. All five modules passed fresh strict checking
and a private-inclusive recursive audit of 260 declarations. Distinct
non-author review is pending. This is not admitted to the main progress checkpoint. The two
copied predecessor files are byte-identical to the separately accepted
four-module rational-parameter packet. New work is in
`ThreeExceptionalParameter318`, `ActualThreeExceptionalParameter318`, and
`ActualThreeParameterProper318`.

## Exact construction

Let a=E4(tau), b=E6(tau), and u be the x-coordinate of the original marked
period 1/3 on the actual normalized Weierstrass curve. The old arithmetic
x-coordinate had scale E6/(12E4), so its formula could not itself be used
at a zero of E4 or E6.

The genuine third-division equation gives, for every tau in the upper half
plane,

    R = 6912 u^4 - 288 a u^2 - 32 b u - a^2 = 0.

Define two rational expressions:

    T1 = 27(144u^2-a)/(a-16u^2),
    T2 = 27(b+4au+1152u^3)/(64u^3-b).

Their cross-multiplied difference is exactly 108uR. Their denominators
cannot both vanish when a^3-b^2 is nonzero: simultaneous vanishing would
give a=16u^2 and b=64u^3, contradicting that discriminant condition.
The glued total function uses T1 where its denominator is nonzero and T2
otherwise. Analyticity is proved from the actual two analytic expressions
and their neighborhood overlap identity. It is not inferred from a
piecewise definition or a set bijection.

The first denominator vanishes precisely when a=u=0 on the nonsingular
third-division locus. The second formula has value -27 there. The formula
therefore resolves the actual formerly indeterminate elliptic branch.

## Binding to the old comparison

On the entire original admissible locus, the original canonical x-scale
is E6/(12E4). Substituting the exact old arithmetic j and x coordinates
into the previously fixed T(j,x) proves equality with this extension.
The source projection theorem identifies it with the original
`LiteralThreeCompactParameter318.sourceParameter`, for every original N.
No newly chosen torsion point, square root, period lift or four-point label
replaces any input.

The discriminant factorization

    (a-16u^2)(144u^2-a)^3 = 1024u^2(a^3-b^2)

on R=0 proves the extended parameter never vanishes in the upper half plane
and gives the exact relation

    J(T) = 1728 a^3/(a^3-b^2) = genuine j(tau).

The modular weights (4,6,2) make both formulas invariant under the original
Gamma1(3) action. Descent is to the actual entire orbit quotient, including
its elliptic stabilizers, with its existing quotient topology. The descended endpoint is a continuous nonzero parameter on that quotient,
exact genuine-j compatibility, and exact restriction to the old comparison.
Holomorphy is proved on the full upper half plane.

## Actual global realization

The target is the punctured complex line with its own inherited topology.
Its rational J map is continuous. The composite of the actual quotient
parameter with J is exactly the original quotient j map.
`ActualJAllLevels318.proper 3` applies at level three without freeness: its
proof descends compact inverse images from level fifteen using the actual
continuous surjective level-forgetting map. This is different from the
N>=5 restriction on the full cusp-atlas construction.

The standard topological theorem that a continuous map into a Hausdorff
space is proper when its composition with a continuous map is proper now
proves properness of the parameter itself. The old admissible parameter
locus is dense: its complement is contained in the roots of the explicit
nonzero polynomial T(T+27)(T+243)(T^2-486T-19683). Every old admissible
parameter is in the actual new image by the exact old inverse comparison.
The proper map has closed image, hence is surjective onto the whole
punctured line. The final period-level theorem supplies an actual tau for
every nonzero T, not only a chosen abstract orbit label.

## Remaining boundary

This does not yet prove that the map on the entire quotient is injective,
nor construct the quotient's complex charts at
elliptic stabilizers. It does not attach the cusps or identify their actual
q-parameters with the projective T charts. No full compact-source
biholomorphism, arithmetic normalization/analytification, PEL identification,
Kodaira-Spencer realization or final contact-height theorem follows.

The previous packet's order calculations concern the specified rational
target J(T). Turning them into local orders on an actual compact modular
source still requires the corresponding source chart/identification.
