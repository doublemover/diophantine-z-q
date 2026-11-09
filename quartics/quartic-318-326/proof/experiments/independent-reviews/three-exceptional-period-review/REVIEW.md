# Distinct bounded review: actual level-three exceptional period extension

Reviewer: `/root/advance_integer_witnesses`.
Producer: `/root/advance_analytic_geometry`.
Decision: **ACCEPT_BOUNDED_NON_AUTHOR_APPLICATION** for the five frozen sources and nine obligations bound in `acceptance.json`.

This is an internal model source/consumer review, not human peer review or a fresh reviewer compiler run. The producer's successful strict logs and private-inclusive audit were hash-verified. No producer source or prior acceptance was edited.

## 1. Exact objects and changed route

The source is precisely `PeterssonQuotient318.Base (GammaOneFiber318.image 3)`, the actual orbit quotient of the upper half plane by the image of Gamma1(3), with its existing quotient topology. `CanonicalXModularity318.standardX` is the x-coordinate of `MarkedPeriod318.standardPoint 3 tau`, not an arbitrary root. `ThirdArithmeticHolomorphic318.standardX_formula` identifies it with the genuine Weierstrass function at period 1/3 divided by `(2π)^2`, and its holomorphy theorem is available on the full upper half plane.

The new target `NonzeroParameter` is the ordinary subtype `{t : ℂ // t ≠ 0}`, with its inherited topology. The construction does not transport a topology from the source or replace the source by an abstract four-element labeling.

The two copied predecessor modules are byte-identical to the prior reviewed rational-parameter packet. That review supports their unchanged algebra; it does not authorize this new extension or properness application. I reviewed the new application separately.

## 2. Full-domain algebra and analytic gluing

The actual order-three point theorem, via `AnalyticThreeSignPoints318.root_iff`, applies to the original standard marked point at every tau. With the actual Weierstrass coefficients `a4=−E4/48`, `a6=−E6/864`, multiplying the third-division equation by 2304 gives exactly

`R = 6912u^4 − 288au^2 − 32bu − a^2 = 0`.

The discriminant condition is exactly `a^3−b^2 = 1728 Δ(tau) ≠ 0`. The two denominators are `a−16u²` and `64u³−b`. They cannot vanish together under that condition. The cross-multiplied difference of the two numerators is `108uR`, so the formulas agree on their actual overlap. The separate polynomial identity checks in `CHECKS.json` independently confirm these coefficients; they are supplementary, not a replacement for the Lean proof.

`glued_analyticAt` does not infer analyticity from the piecewise definition. It proves each rational expression analytic where its denominator is nonzero, obtains the nonzero-denominator neighborhood from continuity, and uses the relation throughout that neighborhood to identify the glued function. This is the correct locality requirement.

On the nonsingular third-division locus, the primary denominator vanishes exactly when `a=u=0`; the secondary expression then has the specified value −27 because b is nonzero. This fills the indeterminate branch without imposing an admissibility hypothesis. Other points above j=0 and all points above j=1728 are covered by the same denominator-cover proof. The discriminant factorization proves nonvanishing of the glued parameter, including its separate u=0 case.

## 3. Exact old-map comparison and normalization

On the entire original admissible locus, the source requires both E4 and E6 nonzero. `scale_formula` derives the original canonical scale as `E6/(12 E4)`, and hence the old arithmetic x-coordinate is `12 E4 standardX/E6`. Substitution into the unchanged rational `parameter(j,x)` gives the primary expression with factors 243, 27, 12, 1728 retained.

`periodParameter_eq_old` compares the functions themselves, not just their j-values. `periodParameter_projection` then consumes the exact original source projection and old x-coordinate theorem for every auxiliary N. `quotientParameter_restrict` covers every point of the old admissible quotient by using an actual upper-half-plane representative and proving its admissibility from the quotient's genuine j-property. No representative-independent formula is assumed without the corresponding proof.

The auxiliary N in `sourceParameter N` is not a replacement for modular level three. Using N=1 in the properness packet is permitted and still consumes the same Gamma1(3) source.

## 4. Genuine modular descent and j identity

The Eisenstein weights are 4 and 6 and the original marked coordinate has weight 2, by `CanonicalXModularity318.standardX_transform`, whose hypothesis is membership in the actual Gamma1(3). The two glued expressions are invariant under exactly those weights with nonzero modular denominator. `image_invariant` then passes through the actual positive-matrix image subgroup.

`Quotient.lift` therefore descends this exact period function to every orbit of the full source, including elliptic stabilizers. Continuity follows from the actual open quotient map and full upper-half-plane holomorphy. This is a continuous quotient coordinate; the packet does not pretend that this constructs a complex quotient atlas at the elliptic orbits.

`J_glued` gives the exact global identity `J(T)=1728 a³/(a³−b²)`. Substituting the discriminant relation yields the original `ActualQJ318.jInvariant`, and `quotientParameter_j` gives precisely `QuotientJ318.jMap 3` after descent.

## 5. Properness: source theorem and actual consumer

I read `ActualJAllLevels318.proper`, `compact_preimage`, `GammaOneLevelMap318.forget`, and the high-level compact-preimage theorem in `ActualJProper318`.

The level-three application is valid. `ActualJAllLevels318` uses the continuous surjective map from level `5*N` to level N and the exact identity of j under that map. For N=3, the properness input is constructed at level15, where the ≥5 cusp-atlas condition is satisfied. Compact inverse images at level3 are the continuous images of those at level15. No false use of a level≥5 theorem directly at level3 occurs.

For the new map f=`fullParameter` and g=`parameterJ`, the equality `g ∘ f = QuotientJ318.jMap 3` is an equality of the actual functions. f and g are continuous, and the codomain of f is the Hausdorff punctured complex line. These are exactly the hypotheses of Mathlib's `isProperMap_of_comp_of_t2`; no injectivity assumption is required. The result proves properness of f itself, not of a substituted source map.

## 6. Density, image identity and surjectivity

The excluded polynomial is exactly `T(T+27)(T+243)(T²−486T−19683)` and is proved nonzero by evaluation at1. Its finite complex zero set has dense complement by the stated topological-vector-space cardinality theorem. Pulling that dense set back under the open subtype embedding of C* gives density in the independently topologized target, not a density statement on a transported target.

For each such admissible target parameter, `admissible_mem_range` uses the inverse of the exact old `sourceParameter 1` and the proved restriction identity. The resulting point is in the range of the actual new full quotient map.

Properness supplies a closed range. A closed subset containing the established dense subset is all of C*. `periodParameter_surjective` further uses actual quotient surjectivity to produce a tau in the upper half plane, with exactly the same period coordinate. The result is stronger than existence of an abstract orbit label, but it does not imply global injectivity.

## 7. Verification and bindings

All five source hashes, six final log hashes, application, intake, README, audit source and receipt bindings were verified. The two predecessor files match the earlier packet byte-for-byte. All211 listed baseline source hashes match both the current files and the stated original commit `5e483a2`.

The private-inclusive audit imports all five modules and traverses every declaration, including private/generated declarations, recursively allowing only propext, Classical.choice and Quot.sound. Its final log reports260 declarations and5 modules. The final compiler logs contain only style/deprecation warnings for `if_pos`, `if_neg` and `Set.mem_setOf_eq`, not proof errors. I did not rerun the compiler independently and do not claim a fresh full upstream rebuild.

## 8. Accepted and excluded claims

All nine obligations in the exact frozen APPLICATION are accepted within the stated scope: genuine full-period holomorphic extension, exact old-map and j identities, actual Gamma1(3) continuous quotient descent, and proper surjectivity onto the natural punctured complex line.

Still excluded: global injectivity on the full quotient; complex charts at elliptic stabilizers; actual cusp attachment and q-parameter/cusp-width identification; compact-source biholomorphism; arithmetic normalization or analytification; PEL, Kodaira–Spencer, represented Picard/Jacobian or metric realization; final contact-height or arithmetic theorem. The previous rational target's branch-order calculations have not thereby become source cusp-order theorems.

No new-gap historical classification is made. This is a new accepted bounded application built from exact prior inputs. The acceptance is invalidated by changes to any bound source, construction, consumer or contract.
