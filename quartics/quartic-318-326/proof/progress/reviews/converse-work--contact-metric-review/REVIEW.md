# Independent review of the actual five-contact metric producer

## Verdict and exact boundary

Accepted at the stated classical arithmetic-geometric application scope. No mathematical mismatch was found in the actual branch model, smooth metric and curvature comparison, vertical extension, or stable-height normalization. This review does not construct Shimura stacks, line bundles, arithmetic degrees, or their realizations in Lean, and does not assert unconditional `FiveContact49Height`.

The reviewed producer is `isogeny-height-transfer/METRIC-PRODUCER.md`, with its normalization ledger and the actual model supplied by `fiber-field-bridge/FIBER-PRODUCER.md`. The literal branch-coordinate arithmetic is independently copied and strictly rebuilt here. The finite curvature and logarithmic constants were already independently copied and rebuilt in `converse-work/five-contact-metric-review`. All numerical and geometric conventions below refer to the actual source objects, not an arbitrary curve with an assumed final height inequality.

## 1. Actual generic model and contact labels

I freshly viewed Gonzalez–Rotger's original printed pages 938–939, including Theorem 4.2 and all four D=210 rows of Table 2. They are exactly the four quartics appearing in `ContactCoordinates318.lean`; the signs and coefficients agree. The quotient-label argument in the fiber producer is valid: genus five and the four genus-one quotients force forty fixed points and a genus-zero full Atkin–Lehner quotient. Tangent faithfulness makes every stabilizer cyclic, hence order at most two. Four known eight-point fixed loci and the product relation supply the fifth label 210. Each label occurs at one branch point and is rational over Q.

Normalize the labels 210, 105, 70 to infinity, zero, one. The residual group on each genus-one quotient has order eight and exponent two. Its translation subgroup is the full two-torsion, so its quotient has the same j-invariant. The four resulting branch-subset j-invariants are therefore those of the four actual published quartics, not four unrelated candidate elliptic curves. The checked invariant identities and six-cross-ratio factorization force lambda=2401 and mu=−343/32. Scaling by 32 gives the actual five contacts 0, 32, 76832, −343, infinity.

The copied strict rebuild here verifies the seven public coordinate theorems and all 21 declarations listed by its recursive axiom audit. Standard roots only are permitted. This is algebraic arithmetic on the actual quartic coefficients; the geometric interpretation of quartic invariants is an explicit standard input.

## 2. Smooth extension and curvature direction

For r_i=|t−a_i|, U=1+sum r_i and P=product(t−a_i), the proposed conformal coefficient is rho=U/product r_i. At a finite branch point t−a_i=z² its pullback is

4(1+|z|²+sum_{j≠i}|a_i−a_j+z²|)/product_{j≠i}|a_i−a_j+z²|.

The exceptional term is |z|², not |z|. Every other factor is nonvanishing near zero, so the coefficient is smooth and positive. At infinity t=z^(−2), put s_i=|1−a_i z²|. The coefficient becomes 4(|z|²+sum s_i)/product s_i, with value 16 at zero. Thus the metric is globally smooth and has no omitted curvature mass.

With K_lambda=−Delta(log lambda)/(2lambda), direct differentiation gives

−K_rho = (product r_i)/(2U³) [U sum(1/r_i)−|grad U|²].

The bounds |grad U|≤4 and (sum r_i)(sum 1/r_i)≥16 leave at least sum 1/r_i in brackets. This is precisely the literal finite curvature quotient already kernel-checked, and gives −K_rho≥1/Cmet. At a maximum of f=rho/(Cmet*h), where h has curvature −1, f>1 would imply Delta(log f)≥2h(f−1)>0, a contradiction. The required direction is rho/Cmet≤h.

Yuan's norm ||d tau||=2 Im(tau) makes the norm of a quadratic differential f(t)(dt)² equal to 4|f(t)|/h_t. Consequently ||q0||≤4Cmet/U and ||q1||≤4Cmet, for q0=(dt)²/P and q1=tq0. The factor four is required and correctly retained.

## 3. Integral extension on the actual maximal stack

Yuan §2.1 states that the maximal model is a regular, flat, semistable Deligne–Mumford stack over Z and, for a division algebra, is proper. Its universal family is an abelian scheme. At a generic point of a vertical component the reduced semistable fiber makes p a uniformizer, and the model is relatively smooth there. Thus relative differentiation kills p and v(du)≥v(u), also for negative v(u).

If v(t)≥0, all r_i=v(t−a_i) are nonnegative and at most one exceeds delta=max v(a_i−a_j). Hence 2max r_i−sum r_i≥−2delta, which yields v(q0),v(q1)≥−2delta. If v(t)<0, all r_i=r, so v(q0)≥−2r and v(q1)≥−r are nonnegative. The literal J=2765952000 is product p^delta. Therefore J²q0 and J²q1 are integral at every vertical codimension-one point. This argument does not require t to extend to a morphism at bad primes; its possible vertical poles have been treated.

Horizontal regularity follows from the same branch charts: q0 is nonzero at finite branches; q0 has a double zero at infinity while q1 is nonzero there. The two sections have no common generic zero. Codimension-one extension on a regular etale atlas extends these rational line-bundle sections across codimension two, and uniqueness descends them to the stack.

## 4. Evaluation, level change and stable height

A generic point of the proper maximal stack may require a finite auxiliary extension before it extends over a ring of integers. This is allowed: after spreading out there are only finitely many missing places, and the proper-stack valuative criterion supplies extensions there after finite field extension. Pullback of the universal abelian scheme gives the stable Hodge height. Normalized arithmetic degrees and stable heights are invariant under that finite extension.

This auxiliary extension is not the degree-bounded isogeny field. It must not be inserted into the 576 or 2304R field-degree estimates. The evaluation uses the pullback of the maximal stack's bicanonical line bundle itself. It does not replace that line bundle by the dualizing bundle on the full-level-three curve, so no level-three ramification correction is introduced. The generic central involution acts trivially on the curve differential and on the surface Hodge determinant. Evaluating at an actual stack point introduces no extra orbifold factor two.

For integral sections with no common generic zero, the ordinary all-place section-height inequality gives h(t)≤height(bicanonical fiber)+2log J+log(4Cmet). Common vertical zeros strengthen this upper bound. The independent `RationalSectionHeight318` packet supplies the actual NumberField arithmetic of this inequality; its bundle/frame interpretation remains geometric.

## 5. Primary normalization ledger

I freshly read Yuan Theorem 1.1 and §2.1, including the rendered primary theorem and page six, and the GR2014 printed 351–352 normalization pages. Yuan's isometric map has image 210 omega_X²:

lambda_A² ≅ 210 omega_X².

With the induced metric, multiplying a lattice by 210 reduces its arithmetic degree by log210. Hence h(omega_X²)=2h_Yuan(A)+log210. Yuan's squared Hodge norm is (2pi)^−2 times the integral; the original dimension-two L² norm is (1/4) times the integral. Therefore h_Yuan=h_L²+log pi, with this sign. The resulting upper bound is

h(t/32) ≤ 2h_L²(A)+2log pi+log210+2log J+log(4Cmet)+log32 < 2h_L²(A)+120.

The shifted GR height is h+=h_L²+log pi, so the same conservative +120 bound remains valid with h+. The shift cancels in same-dimensional isogeny height differences. A degree theorem stated using original height may use the larger shifted height in its maximum by monotonicity, not by silently identifying the two conventions.

The rational contact parameter t/32 here is arbitrary outside the five contacts and need not be positive. By contrast, the auxiliary modular-map value used in the separate finite-divisor argument is 1/(2^128+i) in (0,1). Its positivity is essential for the constant-free horizontal 3h bound. These two parameters must not be conflated.

## Reproduction and retained scope

Run `bash converse-work/contact-metric-review/verify.sh` from the workspace. It compiles fresh copies with `debug.skipKernelTC=false`, executes the copied recursive axiom audit, and byte-compares the copies to the frozen original coordinate sources. `receipt.json` binds the reviewed documents, source PDFs, viewed images and previous independent finite-metric receipt.

The independent maximal-stack/level-pullback binding is being supplied separately by the soundness worker. The independent all-place section inequality is supplied by the mapper and is composed into the final contact metric by the completeness worker. Those refinements remove scalar premises but do not turn the actual algebraic-geometric constructions into Lean scheme/stack realizations. The final global `GeometricRealization` existence and its classical theorem applications must remain visibly distinguished from the kernel implication from such data.
