# Normalize the actual elliptic points and separate their signs

Status: source-policy/dependency checks passed; hosted Lean and distinct source review pending. No local Lean build was run. This is a bounded algebraic prerequisite, not real density or a concrete component-return modulus.

## Construction and exact maps

The unchanged NormalizingRadicals318 copy constructs the actual degree-four field Both over K = Q(sqrt(2)), adjoining sqrt(delta) and sqrt(deltaBar), where delta = 3-sqrt(2), deltaBar = 3+sqrt(2), and delta^2 is the literal source D. Its First-algebra automorphism fixes the first root and negates the second.

The new NormalizedPointSigns318 defines base as the composite of the two literal algebra maps. For v^2 = 1-d^2*u^4 and r^2 = base(d), it proves (base(v))^2 = 1-(r*base(u))^4. Thus normalization is u -> r*u, not u/r. The reciprocal point has coordinates x/r^2 and y/r^3. The zero chart is retained by ReciprocalDouble318.point, so u=0 is not silently excluded; v remains nonzero because the source reciprocal-point constructor requires it.

firstPoint uses exactly D and firstRoot. secondPoint uses exactly deltaBar^2 and secondRoot. Both are actual Mathlib points on E_1: y^2 = x^3-x over Both. They are not a new formal group carrying a presumed law.

flipPoint is an actual additive homomorphism: ShortCurveBaseChange318.pointMap for flipSecond followed by transport along the explicit equality flipSecond(1)=1. The existing base-change theorem supplies preservation of the Mathlib group law. The new transport lemma keeps reciprocal-point coordinates unchanged when only the coefficient is rewritten. Consequently flipPoint fixes firstPoint and negates secondPoint, using the existing actual group-negation theorem point_negative rather than identifying coordinate sign with group sign by assumption.

Applying this endomorphism to m*firstPoint+n*secondPoint=0 and subtracting the original relation gives (2n)*secondPoint=0. If integer multiples of each of these exact points vanish only at zero, then n=0 and m=0. The normalized consumer explicitly retains both nontorsion premises. Coordinate nonvanishing is not used as a substitute for nontorsion.

## Source application coverage and boundaries

Inputs cover all K coordinates satisfying the two displayed source quartic equations, including the zero chart, and all integer m,n. This includes candidate conjugate source points after their coordinate identities are established, but the packet does not itself instantiate the source generator or a conjugation map on its coordinates. It does not construct the normalization as an additive map from the original E_D; only the selective involution on the target E_1 has its group law proved here. An injective normalization/group comparison is still needed to carry the original known nontorsion into the two explicit premises.

No real embedding extension, positive-root choice, circle comparison, character theorem, independent elliptic logarithms, component bound, or intersection of the scalar/guard-good region with the identity component is established here. Even an unconditional integer-relation exclusion would not alone prove real orbit density. The frozen mixed-CRT packet continues to expose the required return multiple and good-region intersection as inputs.

## History and downstream scope

The historical compact-Lie/component argument in quartics/quartic-318-326/docs/arithmetic.md and docs/sources/quartic_v10.tex, lines 10632-10694, remains prior justification found. This alternative algebraic prerequisite is not a finding that the historical argument had a new gap. No accepted baseline, manuscript, first51 assignment, fixed root signs, scalar threshold, prime/CRT conditions, or final source polynomial is changed.

SOURCE-COPIES.json binds the unchanged radical producer. DEPENDENCY-PINS.json binds the exact original reciprocal-point and base-change dependencies. The current packet is not independent proof acceptance; passing structural checks is not Lean elaboration. No browser tabs were opened.
