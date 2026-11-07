# Independent derivation of the actual contact metric producer

## Scope and retained inputs

This is a mathematical proof and source check, not a Lean formalization of differential geometry or Arakelov intersection theory. It uses the actual five-contact model asserted in V10, lines approximately 6930–7094: a compact hyperbolic complex curve X with map t:X→P1, branch values 0,32,76832,−343,infinity, each ramification index two; the corresponding proper regular semistable maximal stack over Z; and Yuan's stated Kodaira–Spencer isometry. Constructing and identifying that Shimura model and its quotient, rather than merely assuming their properties, remains a separate geometric producer.

The finite contact-distance/curvature-quotient theorem is already kernel checked in FiveContactMetricBounds318. This note proves why that quotient is the correct actual curvature input, why the metric has no singularity at the missing points, and why the maximum principle has the required direction and factor four. No estimate on an Arakelov Green function is involved.

## 1. Smooth positive extension, including infinity

Write a=(0,32,76832,−343), r_i=|t−a_i|, U=1+sum r_i, and P=product(t−a_i). On the complement of the branch values put

rho(t)|dt|² = U/(product r_i) |dt|².

At a point over a_i, choose the actual local branch coordinate t−a_i=z². The pulled-back coefficient is

4[1+|z|²+sum_(j≠i)|a_i−a_j+z²|] / product_(j≠i)|a_i−a_j+z²|.

Every nonzero complex constant in this formula stays nonzero in a sufficiently small disc. The norm of a nonzero holomorphic function is smooth as a real function. The expression is therefore smooth and strictly positive at z=0. This does not assert that |z| itself is smooth: the exceptional term is |z|².

At infinity choose t=z^(−2). Put s_i=|1−a_i z²|. Directly cancelling all powers of |z| gives the pulled-back coefficient

4[|z|²+sum_i s_i] / product_i s_i.

It is smooth and positive at zero, with value 16. Thus rho is an everywhere smooth positive metric on the compact curve. These formulas also remove any potential boundary term from the subsequent maximum-principle argument.

## 2. Actual curvature calculation

Use the Euclidean Laplacian Delta=partial_x²+partial_y² and the convention

K_lambda = −Delta(log lambda)/(2 lambda)

for a conformal metric lambda|dt|². Away from the four finite contacts, Delta(log r_i)=0, Delta r_i=1/r_i, and each gradient r_i has Euclidean norm one. Hence

−K_rho = (product r_i)/(2U³) * [U sum_i(1/r_i)−|grad U|²].

The triangle inequality gives |grad U|≤4. Cauchy–Schwarz gives (sum r_i)(sum 1/r_i)≥16. Since U=1+sum r_i, the square-bracketed quantity is at least sum 1/r_i. Consequently

−K_rho ≥ [sum_i product_(j≠i) r_j]/(2U³) ≥ 1/Cmet.

The final inequality is exactly the checked literal-distance theorem, with Cmet=12540153541944538512. The inequalities hold off the branch locus; smoothness of the metric makes curvature continuous, so they extend to the branch points and infinity by continuity. There is no unaccounted singular curvature or Dirac mass on X.

## 3. Maximum principle and Petersson constants

Let h|dz|² be the curvature −1 hyperbolic metric on X. The globally defined smooth positive ratio f=rho/(Cmet*h) reaches a maximum because X is compact. At a maximum with f>1,

Delta(log f)=−2K_rho*rho−2h ≥ 2h(f−1)>0,

contradicting the local maximum test Delta(log f)≤0. Thus rho/Cmet≤h pointwise. This proves the source comparison with the stated direction; completeness at a removed cusp is not being substituted for compactness.

In a uniformizing coordinate tau, h=1/(Im tau)². Yuan's Petersson norm of d tau is 2 Im tau. Therefore the Petersson norm of a quadratic differential f(t)(dt)² is 4|f(t)|/h_t, where h_t is the hyperbolic metric coefficient in t. It follows that

||q0||_Pet ≤ 4 Cmet/U,
||q1||_Pet ≤ 4 Cmet |t|/U ≤ 4 Cmet,

for q0=(dt)²/P and q1=t q0. The first contact is a_0=0, so |t|≤U. The two inequalities extend by continuity at all points. The factor is four, not two, because the section is bicanonical and the cotangent norm contains the factor two.

## 4. Holomorphic sections and the finite-place extension

At t−a_i=z², q0=4 dz²/product_(j≠i)(a_i−a_j+z²), which is regular and nonzero. At infinity t=z^(−2), q0=4z² dz²/product(1−a_i z²) and q1=4 dz²/product(1−a_i z²). Away from these points the map is unramified. Hence q0,q1 are holomorphic and have no common zero on the generic curve.

For a generic point of a vertical component of the semistable regular stack, the base prime p is a uniformizer. Relative differentiation kills p, so for a rational function u=p^r*v with v a unit, du=p^r*dv and v(du)≥r. This is valid for negative r as well. Put r_i=v(t−a_i) and delta=max v(a_i−a_j).

If v(t)≥0, all r_i≥0 and at most one exceeds delta, since a_i−a_j is the difference of the two corresponding functions. Taking the largest r_i yields 2max r_i−sum r_i≥−2delta; this exact finite inequality is checked. Thus v(q0)≥−2delta, and multiplication by t does not worsen it.

If v(t)<0, every r_i=v(t)=r. Then v(q0)≥−2r and v(q1)≥−r, both nonnegative. Therefore J²q0 and J²q1 are integral at every vertical generic point, where J=product p^delta=2765952000. Their horizontal regularity was proved above. On a regular stack, the line bundle is reflexive and checking codimension-one points suffices for extension across codimension two; this is applied on an etale scheme atlas and descends. Semistability and regularity are retained geometric inputs, not consequences of the finite inequality alone.

## 5. Arakelov evaluation and normalization ledger

The global integral sections, with no common generic zero, induce the ordinary height comparison from the section's hermitian line-bundle degree to h(t). Any common vertical zero only strengthens that upper bound. Their archimedean norms are at most J²*4Cmet. Finally h(t/32)≤h(t)+log32.

Let h_L2(A) denote the stable surface Hodge height with squared norm (1/4) integral alpha wedge bar(alpha). Yuan uses squared norm (1/(2pi)²) integral, so h_Yuan(A)=h_L2(A)+log pi. His isometric map has image 210*omega_X². With the induced metric, that sublattice has degree h(omega_X²)−log210. Hence

h(omega_X²)=2h_Yuan(A)+log210
             =2h_L2(A)+2log pi+log210.

This avoids ambiguous use of the word "original" for different Faltings conventions. The displayed Hodge metric, rather than its name, fixes the sign. The numerical bound proved in MetricCancellation318 is

2log pi+log210+2logJ+log(4Cmet)+log32<120.

Thus h(t/32)≤2h_L2(A)+120. If one instead uses the GR/Rémond convention, Javanpeykar Lemma 2.4.4 supplies its explicit dimension-linear correction. The conservative +120 bound remains valid after increasing the height by this nonnegative correction. The relation between the author-version GR definition and the actual L2 convention is separately checked in the normalization source note; no cancellation relies on silently identifying differently normalized heights.

## Conclusion

Conditional on the identified branch model, proper regular semistable stack, and Yuan isometry, the actual finite extension and smooth metric comparison are derived, including all branch/infinity charts and exact constants. The only remaining inputs in this metric subargument are the named geometric constructions/theorem applications, not a new assumed scalar curvature bound or unexplained Petersson factor. The existence of the required fiber, its ramification/level control, the modular Jacobian source map, and the full FiveContact49Height proposition are not proved by this note.
