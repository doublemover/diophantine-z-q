# Explicit level-three boundary parameter

Status: new isolated algebraic/analytic extension experiment. The source is not
part of the admitted progress checkpoint. Lean verification and independent
application review are recorded separately; this document alone is not either.

## Exact source and historical boundary

The source inspected at repository commit `5e483a2` is
`progress/LiteralThreeBaseEvaluation318.lean`, definition `Q`, and the actual
plane type in `progress/LiteralThreePlanePoints318.lean`. The existing
`LiteralPlaneBiholomorph318.biholomorph` identifies the original admissible
Gamma1(3) source with this plane, retaining its independently constructed atlas.
`NaturalPeriodPlaneComparison318` retains the genuine period projection.

The sources and accepted review reports for the plane graph, plane atlas,
period sections and period-to-plane comparison explicitly exclude j=0,1728
and cusps. They do not contain the extension argument below. A focused search
of progress source for a Hauptmodul/rational parameter found none; this is not
a claim about every historical packet. In particular, the historical
disposition of a full global extension remains unresolved.

The actual all-cusp complex structure in
`AllCuspComplexCurve318.actual_compact_complex_curve` assumes `5 <= N`.
It must not be specialized to N=3. The current Gamma-H compact quotient is
topological, with its complex quotient atlas still separate. Thus neither
existing result silently supplies a compact Riemann surface for this N=3
comparison.

## The constructed parameter

Write

    Q(j,x) = (j-1728)^2 x^4 - 6j(j-1728)x^2 - 8j(j-1728)x - 3j^2,
    D(T)   = T^2 - 486T - 19683,
    J(T)   = (T+27)(T+243)^3 / T^3,
    X(T)   = 3(T+27)(T+243) / D(T).

The proposed inverse on the *entire existing admissible plane* is

    T(j,x) = 243 ((j-1728)x^2-j) / (9j-(j-1728)x^2).

No arbitrary root, branch or new point label enters these formulas.

To derive them, put k=j/(j-1728). The quartic becomes

    x^4 - 6kx^2 - 8kx - 3k^2 = 0.

This is quadratic in k. Introducing w by
`3k = -3x^2 - 4x + 2xw` gives `w^2=3x^2+6x+4`.
The rational parametrization through `(x,w)=(0,2)`, followed by a fractional
linear change of parameter, gives precisely J and X above. This derivation
is motivation, not a restriction to x nonzero: the inverse denominator proof
below covers all of the actual admissible plane (where the equation itself
forces x nonzero).

## Full-domain denominator check and both inverse laws

Suppose j is neither 0 nor 1728 and Q(j,x)=0. Then k is neither 0 nor 1 and
x is nonzero. The identities

    f + 8x^3(x+1) = (x^2-k)(3k+9x^2+8x),
    27f - 8x^3(x-3) = -(9k-x^2)(9k+19x^2+24x),

where `f=x^4-6kx^2-8kx-3k^2`, show that neither `x^2-k` nor `9k-x^2`
vanishes. For the first, vanishing forces x=0 or x=-1, and hence k=0 or 1.
For the second it forces x=0 or x=3, and again k=0 or 1. Multiplication by
j-1728 proves both original numerators used in T are nonzero.

Let A=(j-1728)x^2-j, B=9j-(j-1728)x^2 and M=243A. Direct polynomial identities are

    M^2-486MB-19683B^2 = 157464 Q + 1259712 xj(j-1728),
    3(M+27B)(M+243B)-x(M^2-486MB-19683B^2) = -157464 xQ,
    (M+27B)(M+243B)^3-jM^3B
      = 14348907 jQ (Q+16xj(j-1728)).

They give D(T) nonzero, X(T)=x and J(T)=j on every admissible plane point.
Conversely, for T with T, T+27, T+243 and D(T) all nonzero,

    Q(J(T),X(T)) = 0,
    J(T)-1728 = D(T)^2/T^3,
    A(J(T),X(T)) = 8(T+27)(T+243)^2/T^2,
    B(J(T),X(T)) = 1944(T+27)(T+243)^2/T^3.

Thus T(J(T),X(T))=T. These are explicit inverse maps between the original
plane and the affine T-line minus its five specified finite points.
With its inherited complex topology, each direction is rational with
nonvanishing denominator on the complete domain, hence holomorphic.

## Candidate compact target and exceptional points

The projective rational map is the homogeneous pair

    F(U,V) = (U+27V)(U+243V)^3,
    G(U,V) = U^3 V.

It has no common zero on P1: if G=0, either U=0 with V nonzero, giving
F=27*243^3*V^4, or V=0 with U nonzero, giving F=U^4. Both are nonzero.
This specifies a genuine degree-four projective rational map, not merely
a rational formula with an unexamined base point.

Its complete exceptional fibers and local orders are:

- Above j=0: T=-27 has order 1; T=-243 has order 3.
- Above j=1728: the two roots 243+162 sqrt(3) and 243-162 sqrt(3) of D
  each have order 2. They are distinct and nonzero. The identity
  `F-1728G=(U^2-486UV-19683V^2)^2` gives the full fiber.
- Above j=infinity: T=0 has pole order 3, and T=infinity has pole order 1.
  In the latter chart s=1/T,
  `J(1/s)=(1+27s)(1+243s)^3/s`, whose numerator is 1 at s=0.

The derivative numerator is `(T+243)^2 D(T)`, so there are no other
finite critical points off the poles. These fiber/order statements are
ordinary characteristic-zero algebra and local analytic calculations;
the exact meromorphic orders are now proved in ThreeCompactBranchOrders318.
The projective Scheme/analytic morphism registration remains separate.

This explains why the old affine presentation cannot simply be filled.
At j=0, Q becomes `1728^2 x^4`, collapsing two distinct parameter branches
to the same x=0 point. At j=1728, Q is the nonzero constant
`-3*1728^2`, so there is no finite x point. A normalized/projective target
or other chart is essential.

## Exact remaining global join

The fourth module composes the existing original comparison with T and
proves an analytic equivalence with the independently natural open-subspace
parameter atlas. The next step must construct or independently identify the full N=3 quotient
complex atlas at elliptic stabilizers and the cusp charts, and show that
the omitted points match the six projective boundary points above with
the actual local orders. Establishing that match would extend the
admissible comparison to the specified compact analytic source.

The following are not concluded here: scheme-level normalization of the
original compactified arithmetic model, analytification, general-N modular
or PEL comparison, represented Jacobian/Picard schemes, Kodaira-Spencer,
metric/source realization, or FiveContact49Height. An abstract compactification
by the displayed P1 alone does not identify those original objects.

## Verification contract

The independent algebra module defines the same displayed polynomial.
A separate consumer must bind it by definitional equality to the existing
Q and compose with the actual old maps. Proof obligations include all
admissible points, both inverse identities, nonzero original denominators,
unchanged j/x functions, and the exact N=3 source. No generic-only argument,
point count, transported atlas or unproved compact-source identification
may replace these checks. Successful symbolic identity checks do not
constitute Lean compilation or independent acceptance.
