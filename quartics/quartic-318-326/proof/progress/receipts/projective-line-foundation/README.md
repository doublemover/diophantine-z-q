# Actual projective O(1) and its contact pullback

This packet constructs the target line sheaf independently of the contact
bicanonical sheaf, using the actual two standard charts of the genuine Proj
projective line over Q. It then constructs its actual sheaf pullback along the
already checked section-defined contact map. It does not yet identify that
pullback globally with the intrinsic bicanonical sheaf.

## Actual target construction

`ProjectiveLineOverlap318` constructs the entire common chart as
Spec(Q[t,t^-1]), with both actual chart inclusions and their commuting Scheme
square. It proves the exact full image intersection and the categorical
pullback. The overlap coordinate t and its inverse s satisfy t*s=1.

`ClutchedModule318.sheaf` is a categorical pullback in the category of actual
O-modules. Its two projections are the local coefficient maps, subject to the
specified restriction equation with transition multiplication. This definition
does not assume local freeness. `ClutchedModuleFrames318` proves genuine local
frames on both charts when the chart ranges are the full intersections and
the transition function is a unit. Restriction preserves the relevant finite
limits by evaluation on abelian-group presheaves; no flatness hypothesis or
unproved descent assertion is inserted.

`ProjectiveLineOOne318.line` specializes this construction with
finite-coefficient = t * infinity-coefficient. Thus its frame convention is
e0=t*e1, the usual O(1), rather than O(-1). Its `finiteFrame`, `infinityFrame`
and `frames_cover` provide actual rank-one trivializations covering every
point of the target. The construction is not a renaming of the source's
intrinsic tensor-square module.

`ProjectiveLineCoordinates318` constructs two genuine global target sections
with local coefficient pairs (1,s) and (t,1). All four projection equations
are checked. The four named proof specializations use inferred proposition
types to retain the exact chosen categorical limit; their bodies apply the
checked generic theorem. They are audited definitions, not axioms. A redundant
concrete morphism-alias draft timed out during elaboration and is excluded.

## Actual source pullback

`PullbackLineFrames318.chartIso` uses the actual pullback functor, its composition
and equality comparisons, and the canonical restriction/pullback isomorphisms.
`frame` then uses the canonical pullback-of-unit isomorphism. These constructions
require an actual commuting chart square but no flatness assumption.

`ContactProjectiveLinePullback318.line` is the literal pullback of the separately
constructed target line along `ContactBicanonicalProjectiveMap318.projectiveMap`.
Its `branchFrame` for every i:Fin4 and `infinityFrame` use the previously proved
exact coordinate-map squares. They are frames of this actual pullback, not
frames of the intrinsic cotangent square substituted by definition.

## Remaining comparison

A global isomorphism from this actual pullback to Omega tensor Omega, carrying
the pulled coordinate pair to the actual contact q0/q1, remains to be built.
The target coordinate projections are checked here; the full naturality and
frame normalization of the pulled coordinate maps is part of that next join.
No PEL identification, Shimura twist selection, Kodaira–Spencer map, metric
normalization, genus, complete-linear-system or height assertion follows here.

## Validation

Nine fresh strict source replays and a joined recursive audit of 64 modules /
935 declarations pass, with 101 new declarations and only propext,
Classical.choice and Quot.sound. This is a bounded packet replay, not a clean
whole-repository audit. Source/dependency hashes and nine application obligations
are frozen separately. Non-author application review is separate and pending.
