# Construct the actual additive circle comparison

Status: source-policy and dependency closure passed; hosted Lean and distinct review pending. No local Lean compilation was run. This43-source superset adds three substantive sources to the joined40-source route and repairs one exposed simplifier-name collision.

## Actual invariant clock

OvalInvariantClock318 starts from the retained full real oval parametrization

u(t)=sin(t), v(t)=cos(t)*sqrt(1+sin(t)^2).

Its invariant speed is speed(t)=1/sqrt(1+sin(t)^2), positive, continuous and2*pi-periodic. Define clock(t)=integral from0 to t of speed. The fundamental theorem of calculus gives its exact strict derivative. Positive derivative makes clock strictly increasing. The periodic-integral bounds give limits at both infinities, hence clock is onto. Its actual order inverse angle is constructed, not postulated.

The positive period is clock(2*pi). The exact clock shift implies angle(s+period)=angle(s)+2*pi. The inverse-function theorem gives angle'(s)=sqrt(1+sin(angle(s))^2). Reparametrizing the original full oval by angle produces a continuous periodic surjection flow:R->Oval1 with flow(0)=(0,1) and exact coordinate derivatives

u'=v, v'=-2*u^3.

This construction includes both u=0 points and both v=0 endpoints. No branch is omitted and no arbitrary additive structure is transported to make the parametrization additive.

## Actual group additivity by uniqueness

OvalFlowAddition318 uses the polynomial vector field F(u,v)=(v,-2u^3). The whole unit quartic oval lies in the closed radius-two ball in R^2. F is proved C1; the existing compact-convex C1-to-Lipschitz theorem supplies a uniform Lipschitz constant on that actual ball. The existing global ODE uniqueness theorem then applies to any two oval trajectories with the displayed derivative and the same initial point.

The new tangentU and tangentV identities are exact rational identities for the original sumU/sumV formulas. Their denominator1+u^2*a^2 is strictly positive. Differentiating a trajectory plus a fixed actual oval point gives the same polynomial vector field. The polynomial reductions use only v^2=1-u^4 and b^2=1-a^4; no exceptional tangent, inverse, or zero-ordinate cases are discarded.

For each fixed t, the trajectories s->flow(s+t) and s->flow(s)+flow(t) solve the same ODE and have the same initial value at s=0. Uniqueness proves flow(s+t)=flow(s)+flow(t) in the existing RealQuarticGroup318.group. Thus flowHom is a genuine additive homomorphism, and its surjectivity was already constructed by the clock.

The tangentV numerator was also checked by exact symbolic polynomial reduction: its remainder modulo v^2+u^4-1 and b^2+a^4-1 is zero. This supplementary algebra check is not Lean elaboration or proof acceptance; the Lean proof contains the explicit linear-combination identity.

## Exact kernel and topology

OvalAddCircle318 proves flow(s)=0 if and only if s is an integer multiple of period. In the forward direction, the actual identity coordinates force sin(angle(s))=0 and cos(angle(s))=1. The exact trigonometric kernel theorem makes angle(s) an integer multiple of2*pi; the periodic integral theorem then makes s the corresponding integer multiple of period. The reverse direction uses the proved period and flow(0)=0. The second u=0 point, with v=-1, is correctly not in the kernel of this flow.

The actual quotient homomorphism therefore induces circleAddEquiv:AddCircle(period) equiv+ Oval1. Its continuity descends from the continuous real flow through the quotient topology. Compactness of the positive-period additive circle and Hausdorffness of the original real oval subtype make this same equivalence a homeomorphism. The target law and topology remain the original ones throughout.

## Consumer and remaining work

The copied normalized-generator route already reaches integer independence of the exact normalized coherent oval generators. This packet supplies the previously missing additive-circle and topological comparison for that same Oval1 group. The original scaling equivalences/homeomorphisms connect the two source coefficients to Oval1.

The product-circle density/character-separation theorem is still needed: integer independence of the two specific circle elements must imply density of their diagonal integer orbit in the product. No such implication for an arbitrary compact group is asserted. DenseOrbitCRTPrefix318.select_prefix_of_dense therefore still displays DenseRange of the literal original pairOrbit as a premise. Once that theorem and the exact product transport are supplied, its already constructed m=1, fixed guard margins, scalar-good generator and same-h mixed-CRT/first51/sign consumer apply unchanged.

The final237 source rows and the separate prime-pattern/local scalar arithmetic remain outside this packet. No full318/326 theorem is claimed.

## Hosted repair, source identity and history

Run42578244224 ataa07a2c passed23 predecessors, including the repaired real coherent orbit, before ActualCyclicClosure318 failed. The namespace had opened RealQuarticGroup318, so its local zero_add theorem shadowed the generic zero_add in a restricted simp list. The new copy explicitly uses _root_.zero_add; no subtype group, orbit or recurrence theorem is changed. The exact tested40-source bytes, RESULT and failure log are preserved there under hosted-failure-42578244224. The new clock/flow uses also qualify that generic identity.

SOURCE-COPIES.json binds39 unchanged sources, this one repaired source, and the three new clock/flow/circle sources. DEPENDENCY-PINS.json binds125 baseline predecessors. All prior radical, DecidableEq and scalar-argument repairs remain unchanged in their current copies. No accepted manuscript or baseline is changed.

The historical compact-Lie/component argument retains its prior-justification-found status. The new explicit clock route is formal progress toward the current real-density join, not a newly discovered historical gap. Structural checks and symbolic calculations are not Lean elaboration or mathematical acceptance. No browser tabs were opened.
