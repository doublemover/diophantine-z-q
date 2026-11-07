# Independent final five-contact assembly review

## Result and exact scope

The two frozen modules were copied into this review directory and independently rebuilt with Lean 4.35.0 and `debug.skipKernelTC=false`. Their complete module-declaration axiom audits passed: 87 declarations for `FiveContactProducer318`, and 8 for `ContactMetricSections318`. The only roots are propext, Classical.choice and Quot.sound. These counts include structure projections and generated declarations; they are not counts of new geometric theorems.

The mathematical review accepts the assembly's primitive-coordinate, branch/infinity, CM/non-CM, field-role, normalization and final-constant linkage. No mismatch was found in that scope. This is a review of the exact theorem applications and their composition, not a new independent proof of every cited global theorem or a fresh original-source audit of every other worker's packet.

The top theorem is correctly conditional:

    GeometricRealization -> ContactHeight318.FiveContact49Height.

**GeometricRealization remains unproved in Lean.** Neither this copied replay nor the classical producer notes eliminate it. The two branches retain explicit geometric data and identifications; neither simply assumes the desired final contact bound.

## 1. Primitive coordinate and all five contacts

The actual five forms are v, u, u-v, u-2401v and 32u+343v. Nonvanishing gives v nonzero and s=u/v distinct from 0, 1, 2401 and -343/32. Thus infinity is excluded by the first form rather than lost through division. The other four exclusions are proved by cross multiplication with a genuinely nonzero denominator. Coprimality is the upstream primitive-input condition, although these elementary exclusions themselves do not need it.

The metric uses t=32s. There are four finite branch factors at 0, 32, 76832 and -343; infinity is the fifth branch value, not a fifth finite product factor. For a nonbranch input, q0=(dt)^2/product_(i=0)^3(t-a_i) is nonzero at the chosen point, so the section wrapper's a0 nonzero premise is supplied by the actual geometry. Its section ratio is precisely t. No common vertical nonzero condition is imposed or needed: integral sections may have common vertical zeros, with the favorable inequality direction checked by the all-place section theorem.

`pointHeight_eq_contact_height` is the exact actual rational/projective height equality; `scaled_metric_height` returns from t/32 to s. `support` is literally B_bad times the actual odd-contact radical, not an arbitrarily enlarged support. `support_ge_one` uses positivity of those products. In the global geometry the actual primitive-contact support is provided by the fiber/conductor ledgers. It is not silently inferred from the positivity theorem alone.

There is no positivity restriction on s. The later modular non-Weierstrass fiber is selected above an unrelated auxiliary a_i=1/(2^128+i) in (0,1). That positivity is essential for its finite-divisor bound but does not constrain the original contact input.

## 2. Why the surface branches are exhaustive

The selected surface A has an action of a rational quaternion division algebra B. Over an algebraic closure, if A is simple, End^0(A) is a division algebra acting on its four-dimensional rational first homology. Its dimension divides 4. The inclusion of B forces it to equal B. A quaternion division algebra has no commutative semisimple subalgebra of dimension 4, so this case is not CM.

If A is not simple, Poincare reducibility gives two elliptic factors. Distinct nonisogenous factors have a commutative product endomorphism algebra, which cannot contain B. A repeated non-CM elliptic factor has endomorphism algebra M2(Q), into which a four-dimensional division algebra cannot inject: equal dimensions would force an impossible isomorphism. The remaining nonsimple case is E^2 for a CM elliptic curve. Conversely this is the possible CM branch. This verifies the dichotomy used by the two data records; an intermediate non-CM product branch is not omitted.

The same-field CM argument was read in the CM producer. Rational idempotents are defined over L by geometric endomorphism descent; the resulting elliptic subvarieties and their homomorphisms are defined there. The maximal-order quotient is explicitly constructed over L. Its tangent action embeds the imaginary quadratic CM field in L, so the fundamental discriminant support follows from the discriminant tower. These are genuine classical geometric antecedents for the record fields, not consequences of the final numeric CM theorem.

The non-CM branch therefore has the absolute simplicity needed to make a nonzero A-to-J_H map have finite kernel and image dimension 2. This also supplies genus at least 2, as required by the cusp, Wronskian and Arakelov estimates.

## 3. Fields and coefficient fields do not get interchanged

The roles are distinct throughout:

- L is the controlled normal fiber field, of degree at most 576. It controls CM factor/isogeny data and ramification support.
- L' is the controlled sign-lift field in the non-CM branch, of degree at most 2304R. It is the field used in the dimension-two isogeny degree estimate and the A-to-J_H Hom argument.
- K, or the CM averaging degree q, may arise after an auxiliary extension to evaluate integral models, stable heights and all complex embeddings. Its degree is not inserted into a bounded-isogeny formula.
- The modular newform coefficient field is an auxiliary coefficient field for the Tate representation. All coefficient conjugates are retained in the modular factor, and coefficient extension of Hom spaces does not enlarge L'. It is not a field-of-definition degree multiplier.

The `NonCMData` type parameter K is expressly the auxiliary model/averaging field, while `isogenyFieldDegree` is a separate scalar with the correct 2304R bound. The CM record likewise separates `averagingDegree` from `fieldDegree`. Stable normalized degrees and the actual rational base-change height identity justify allowing unrestricted auxiliary K.

## 4. Actual modular and metric identifications

The exact point-level modular factor, diamond-kernel quotient and degree are supplied by the modular-factor producer. The point-level and mu_N models are related by the rational dual-isogeny/Fricke map, not identified by an invalid rational-cusp convention. The full coefficient-conjugate span is retained. The actual degree formula includes -I on both sides, so there is no extra factor 2. The actual integral-cover producer supplies vertical support p dividing 6N even if the order of H is not inverted.

The conductor and finite-index results give N<=210^300 R^2 and d<2^14*210^300*R^(97/32). The log-growth exponent is R^(1/32); the actual squared Jacobian bound therefore has exponent 2*(97/32)+2*(1/32)=49/8. This is not a repackaged older exponent-24 estimate.

At the original quaternionic point, forgetting the full level marking gives the same surface A on the maximal stack. Yuan's n(U)=1 theorem has image210*omega_max^2, so its actual evaluated degree is

    h(omega_max^2)=2h_Yuan(A)+log210
                  =2h_L2(A)+2log(pi)+log210.

The sections and their metrics belong to the pulled-back maximal canonical line. They are not reinterpreted in the dualizing line of a level-three cover. Hence no ramification divisor or level-degree correction occurs. The central -1 acts trivially on the rank-two Hodge determinant and on the base cotangent line; no factor from global stack integration is involved in point evaluation.

The fresh `ContactMetricSections318` replay proves the contact comparison from actual NumberField section coordinates/frame norms, their finite integrality, their archimedean bound J^2*4*Cmet, and the exact normalized line-degree identification. Rational scaling costs log32, and the checked additive budget gives the strict original-normalized bound h(s)<2h_L2(A)+120. The shifted wrapper then weakens this correctly. It does not assume that same contact inequality as a premise.

## 5. CM and non-CM numerical consumers

For CM, the actual producer yields original-normalized surface height below 854R. The final assembly uses the factor 2 and additive 120 from the contact metric comparison. It does not apply the obsolete generic lemma which assumed contact height itself at most 854R. Reduced periods, the eta/Silverman equality, product additivity, the actual Xi-squared isogeny bound and half-log variation remain visible fields until their geometric realization.

For non-CM, the data contain actual local cusp functions, their holomorphic disc energies, nonzero Wronskians, a finite intersection matrix/section datum and the three exact Arakelov identifications. They do not contain a final Jacobian-height bound. Metric cancellation uses the same local coordinate and the same k=g(g+1)/2 at each embedding. The complex embedding average has the actual number-field degree denominator. The original-to-shifted correction is dimension-linear with the correct sign.

Image-height monotonicity and the dimension-two isogeny variation are named intermediate inputs, and the source notes identify their actual geometric meanings. Their composition gives the required surface bound and then the exact final contact constant 2^68*(210^300)^2*R^(49/8)+128. The global record does retain the intermediate `contact_metric` field; the subsequently checked section wrapper derives that field from more geometric data. It should not be described as already instantiated in the frozen global module.

## 6. Precise formal realization still absent

A full unconditional Lean conclusion still requires constructing, for each primitive noncontact rational point, actual data in one of the two record branches. Current code does not construct the following global objects and their exact identifications:

1. The actual Shimura/fine/maximal-stack fiber and universal abelian surface, controlled number fields, reduction/ramification support and same-field Hom descent.
2. The actual Hodge and bicanonical line bundles at that point, their frame norms and integral sections, and Yuan's normalized-degree identity for that object. The ordinary NumberField section-height calculation is already proved; the model identification is classical.
3. In the CM case, actual periods/CM field and the stable Silverman/product/isogeny identifications.
4. In the non-CM case, the actual modular representation/factor/cover, its cusp differential coefficients/global L2 interpretation, and the actual regular model, intersection matrices, sections and local different interpretation.
5. The exact minimal-model, Faltings-Wronskian, normalization, image-height and isogeny theorem applications for those objects.

The existing classical producer notes trace these constructions and named theorem applications. The finite and analytic Lean results remove many constituent inequalities. They do not manufacture a term of `GeometricRealization`, and this review does not assert one. No axioms, sorrys or unchecked native computations were added by this review.

## Reproducibility

Run `bash global/build.sh` and `bash metric/build.sh` from this directory's copies. They compile the exact frozen source copies against the recorded shared dependency cache, then audit every declaration belonging to each module. `receipt.json` and `REVIEWED_SHA256SUMS` record the source/log/input hashes. These are bounded independent replays of the two named modules, not a fresh rebuild of their entire imported dependency closure.
