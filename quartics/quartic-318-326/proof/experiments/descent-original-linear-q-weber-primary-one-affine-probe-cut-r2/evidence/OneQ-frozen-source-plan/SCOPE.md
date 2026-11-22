# One-Q phase comparison, direct faithful affine lift

Source-only, text-only. The three recovered Lean sources are
byte-identical to the first-written checkpoint. No build, packet
staging, archive, hosted assertion or remote changes.

## Exact output on the same generic curve

The pole, cap, stationarity and generic power shapes are **inputs from
other gates**, not consequences of agreeing with a known value at Q.
ActualGaussianWeberPrimaryOneAffineProbe318.positive_powers_from_same_named_probe
takes the original scalar's hGeneric, namely its actual signed affine
point equality in the one function field k(E), plus the four pure-power
branches from PurePower33 on the exact same u,v and chosen i. The primary
conditions are a=1−2(c+d), b=2(c−d). Its output is the pair of literal
equalities u=(xGeneric k)^p and v=(yGeneric k)^p. It does not choose
a new R, a new point, an extension of the residue place or a new sign.

The point Q=(i,1−i) is the actual order-four point in E(k), with
2Q=2JQ=T0=(0,0). For the primary a,b it is fixed by [pi].
Instead of moving an origin point by Q, choose the genuine affine
Hensel lift over the same k[[t]]: X=const(i)+t, and solve the monic
Y²−(X³−X)=0 near const(1−i). Its derivative at the lifted
approximation is a unit because its reduction is 2(1−i)≠0.
X is nonconstant (actual t≠0), so the existing polynomial and
quadratic-chart embedding is faithful. The old broader two-point
interpolation is unnecessary once the four pure branches are known.
This sieve of generic branches does not prove stationarity.

Exact stock coordinate covariance transports hGeneric, with the same
i, to this actual affine lift. Fixed-X/Y p-power formulas now give
integral polynomials, no denominators. The actual existing reduction
homomorphism and compatible positive quarter-turn mean
red([pi]M)=[pi]red(M)=[pi]Q=Q. The two coordinates of Q are nonzero and
p-fixed for the explicitly named carrier below, so all three wrong
tags are excluded. This is a faithful generic transfer, not an
identification inferred from a finite set.

## Carrier and p-fix are not free

Let s=rootOf (p:=p) a b and hs=rootOf_sq (p:=p) a b hN. For assembly
with Descriptor62 and derivative38 take exactly V=BasePlace s hs,
k=ResidueField V, i=residue V (integralI s hs). The strict
ActualGaussianWeberSelectedGaussianPrime318.residueEquiv s hs is
a ring equivalence k ≃+* ZMod p, and residueEquiv_i sends this i to s.
Do not choose another square root of −1 or use complex I for i.

The final assembly can supply the phase theorem's CharP and hiFixed
directly from the strict source and the pinned stock finite field
theorem. With e=residueEquiv s hs the following is the exact intended
independent proof term (not an additional source owner):

    let e := residueEquiv s hs
    letI : CharP k p := ⟨fun n => by
      have he : (n:k) = 0 ↔ (n:ZMod p) = 0 := by
        rw [← map_natCast e n, ← map_zero e, e.injective.eq_iff]
      exact he.trans (CharP.cast_eq_zero_iff (ZMod p) p n)⟩
    have hiFixed : i ^ p = i := by
      apply e.injective
      rw [map_pow]
      exact ZMod.pow_card (e i)

Mathlib pin 56a005855ea17e0b0958f73ec801ae140b0a1679
FieldTheory/Finite/Basic.lean:589 gives
ZMod.pow_card (x : ZMod p) : x ^ p = x under Fact p.Prime.
For the chosen extension residue (not assumed equal to ZMod p),
the separate strict ChosenPlaceLift.chosenEmbedding_i puts this
one i in the embedded prime field and actual_residue_char gives
the matching characteristic; that shows i^p=i but does not assert
that all extension constants are p-fixed.

## Later Frobenius assembly boundary

The generic terminal combines the four gate outputs on the same
hGeneric point: descriptor's normalized R and u,v, actual selected
cross derivative on that R, actual generic pure-power shapes from the
same cap/pole and then this phase result. The p-power stock coordinate
map on k(E) is the one given by frobenius and the same original model.
No generic-to-all-points or arithmetic/Weber/rank statement is claimed.

For the actual all-geometric-points step, an alternative paper route
avoids evaluating a rational function at a possible pole. Over an
algebraic closure K of the actual residue field, work in L=K(E) with
the generic stock point T. For any constant P in E(K), T+P is neither
infinity nor constant: otherwise subtract P to make T constant.
Its x is transcendental over K: if algebraic, algebraic closedness
makes x constant, and y²=x³−x gives constant y (choose a square root
over K and factor the difference of squares). Thus literal
ArcFunctionEmbedding faithfully sends the base generic point to each
of T and T+P over the same L. Coordinate covariance and p-power
naturality transport the already-proved generic equality to both.
Subtract using both true stock additive maps, then descend the result
for P using the injective constant coordinate map. No finite-point
set determines a morphism here. This is an eventual separate proof;
the current phase imports do not formalize this arbitrary-P step.

Even after that, arithmetic torsion comparison must use the strict
point-reduction arithmetic Frobenius at the actual over-place, the
literal compatible selected i, and strict prime-to-p torsion
injectivity on that same reduction map. No implication about
rational points is introduced by the phase.

## Exact local scope and proof limits

31/0 with 28 authenticated strict Origin31r5 source/log donor bytes,
the old unchanged source-only PrimaryProbe, and two new source-only
owners. Independent 5/0 FixedXAffineHenselProbe is one new owner
over the strict PowerSeriesArc closure; separate 5/0 PrimaryProbe is
one old source-only owner over strict donors. The residual p-fix
supply is a strict **external** carrier proof, not a project import.
No Mixed9 first-jet, origin-pole, descriptor, derivative, or broad
point-level Frobenius gate is imported. StockReductionAdd's old,
already strict mixed geometry remains an indirect donor for the
actual reduction homomorphism. All package metadata here is plain
text and local; no local Lean invocation or validation of the
three source-only bodies is claimed.
