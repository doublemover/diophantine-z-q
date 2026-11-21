# The ordinary cotangent of the actual marked point

This is a constructor for the exact missing ordinary specialization in
the earlier finite/archimedean matched tensors, not an adapter assuming
that specialization. The fixed point is the original noncontact
t=32u/v and the same marked D=210 surface. Work on either proper fine
trait (level 3 outside 3, level 11 at 3), initial height field L,
and the exact MarkLocal B=A_P of the original closed stalk A, embedded
in its actual function field. Evaluation of B, not of the function
field, is the already chosen map to L.

## The geometric input is small and precise

On the original finite noncontact open of the maximal curve the
literal ordinary chart has the four equations y_i^2=c_i(t-b_i),
with b=(0,32,76832,-343) and c=(-14,-6,42,-21). No other
equations or coefficients are substituted. Invert the product
of the four nonzero roots on this chart. The equations are finite
free before this localization (monic in each root, basis of the
16 squarefree monomials). Each inverted root has unit Jacobian
entry 2*y_i over Q. The resulting map to the t-axis is étale.
For an independent infinitesimal check, if I^2=0 and x is any
lift of a residue root, set

    root = x + (c_i(t-b_i)-x^2)/(2*x).

Each 2*x is a unit since its image is a unit modulo a nilpotent ideal.
The error term lies in I. The new value solves the exact equation
by I^2=0, and uniqueness follows by subtracting equations in the
same residue class. Do it independently for all four ordered
roots and keep the same lifted t. This is the exact square-zero
lifting criterion; localization imposes no further choices.
SelectedLiteralOrdinaryRootLift318 ports this arithmetic step
and simultaneously keeps the four labels.

The full fine level over Q is a finite étale torsion-mark cover of
the smooth maximal moduli stack. The coarse maximal curve has no
geometric extra automorphisms beyond its generic sign: an extra
O-linear stabilizer would give an embedding of Q(i) or Q(sqrt(-3))
in the quaternion algebra, impossible since 5 and 7 respectively
split in those quadratic fields but ramify in the quaternion algebra.
Thus passage from a full fine level to this coarse chart is étale
also on the indicated ordinary open. One may equivalently check it
on the common fine level 33 at the same marked generic object. The
remaining geometric identification is the true representability and
ordinary chart of this actual fine model, not an explicit new algebraic
point or an arbitrary formally étale substitute.

The second geometric fact is that the **actual** fundamental map
Omega^1_{A/Z} -> W to the relative dualizing stalk becomes an
isomorphism after base change to B. Indeed the generic noncontact
point is smooth in characteristic zero; on the smooth locus the
dualizing sheaf is the relative top Kähler differential sheaf and
the fundamental map is its canonical identification. The use of
Omega over Z versus Q is harmless on B: localization Q/Z has zero
relative differentials and the usual localization theorem applies.
See [Yuan v2, §1 and §2.1](https://arxiv.org/pdf/2205.11334#page=3)
for precisely this actual fundamental map and fine model.

## The native producer removes free frame and point-comparison data

SelectedActualMarkedOrdinaryAxis318 first constructs Q acting on
the actual B, because no nonzero integer is killed by the chosen
field evaluation. It makes the one-variable polynomial action
by sending the polynomial variable to the **already fixed t-germ**.
It also derives that a nonzero actual value of a germ makes it
a unit in B, not necessarily in the integral closed stalk A.
The precise formal-étaleness input is for this action, not for
some abstract search for an ordinary coordinate.

SelectedOriginalOrdinaryCoordinateCotangent318 then uses the
pinned Mathlib polynomial Kähler basis and the formal-étale
tensor Kähler equivalence to produce a linear isomorphism

    Omega^1_{B/Q} -> B,  d(t) |-> 1.

The source uses the inverse tensorKaehlerEquivOfFormallyEtale,
not just the vanishing of relative Omega for an unramified map.
The isomorphism commutes with every same-axis tower between such
actual rings: d(t) maps to d(t), so one checks the full map on
the literal one-generator basis. In particular its specialization
at the actual point still takes the nonzero cotangent d(t) to 1.

SelectedActualFundamentalCotangentPull318 now constructs the
specialization of W directly: extend the original fundamental
map by tensoring, invert that map on B, apply the canonical
Kähler map from the arithmetic forms, then the derived d(t)
coordinate and actual residue-field evaluation. The source proves
the base-change identity for every integral generator d(a) using
KaehlerDifferential.map_D. Thus the terminal ordinary_at_mark
produces, for the given A and B, the exact pair D and sigma needed by
the earlier actual_dt and match_finite_to_archived: D(t)=1,
the field-valued Leibniz rule, and the integral comparison
D(a|_B)=ev(delta a)*sigma(e) for the same primitive e. No freestanding
point differential function or comparison-on-generators is supplied
as an assumption. No new geometric coordinates or orientation
choices appear.

## Scope and next hosted unit

The generic/formally étale fine-chart and invertibility of the
base-changed true fundamental map remain classical input fields
for the actual scheme, with the precise proofs above. Full moduli
representability, polarized abelian-scheme cohomology and the
comparison with the actual KS map as constructed by Yuan are not
formally derived. This is not an end-to-end native proof.
The genuinely small next-hosted operators are
SelectedOriginalOrdinaryCoordinateCotangent318 and
SelectedLiteralOrdinaryRootLift318; then test the two actual
closed-/generic-stalk modules against the unchanged same-section
donors. No local Lean build or remote writes.

    sha256sum -c SHA256SUMS
    python3 check_ordinary_axis.py | cmp - EXACT-ORDINARY-AXIS.json

The finite-ring replay independently enumerates unique lifts at five
rational primes of each of the literal four equations; it verifies
both the Newton correction and its coefficient-of-dt derivative.
These are controls of exact algebra only, not actual D210 special
fiber computations or substitute geometry.
