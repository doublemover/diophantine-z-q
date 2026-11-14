# Independent Siegel inverse and normalizer-quotient review

Verdict: no source or supplied human application-contract preservation blocker found. This is an independent source/API/contract review of the two frozen candidates, not Lean acceptance. The previously authored Sphere annotation report remains unchanged. Final packet nine-obligation metadata and propagation are separate.

## Siegel normalization

Candidate cdc23bb0b1eef4253d178243303869d95a930db6ce4c7942e1f50db0e91c40c1 replaces only the two inverse proof bodies. The authentic torsion-r21 artifact shows four residual inverse goals involving explicit Fin constructor applications and beta inverse monomials. No later period proof error is interpreted as a module pass.

The new proof is a substantive coordinatewise arithmetic route. In denormalize(normalize z), x is the existing second normalized coordinate and hx follows from native div_mul_cancel₀ with the already proved beta_complex_ne. On coordinate zero, the difference of the (1-beta)/2 and (1+beta)/2 terms is exactly beta*x; the displayed calc uses hx, commutativity and cancellation of the same tau. On coordinate one the identical correction terms cancel. Every Fin2 coordinate is covered by funext/fin_cases; the explicit change spells the same original expressions with indices zero and one.

In normalize(denormalize z), A and B name the original two linear combinations. div_eq_iff applied to parameter_ne proves tau*A/tau=A via mul_comm. Subtracting B gives exactly z1*beta by ring, and div_eq_iff with beta_complex_ne gives the original second normalized coordinate z1. Substitution into B-(1-beta)/2*z1 gives z0. Signs, halves and coordinate order were checked directly. These local equalities need only the two existing derived nonzero facts, not beta squared equals five; no premise or altered parameter domain is introduced.

Both public inverse statements and all bytes before them and from normalization onward remain identical. The normalize/denormalize functions, upper-half-plane input, full complex vector space, exact original periods, lattice equivalence, Hermitian form, quadratic phase and theta factor are not replaced. normalization consumes the two proofs directly; PELOriginalGaugedTheta318 consumes original_period and PELOriginalThetaHermitianGauge318 consumes normalized_factor_formula. These exact original consumer sources were inspected and bound.

Pinned Mathlib GroupWithZero/Units/Basic.lean blob 2f646d87fae7e4f7219c2ddac7313976fadf9f5d independently confirms div_mul_cancel₀ and div_eq_iff with the exact argument order used. Whether each concrete vector change elaborates within the unchanged limits still requires hosted Lean; no broad field_simp-cause claim is made.

## Actual normalizer parity quotient

Candidate e55b17023b6c64aeef373bae82792af4d890fc55c1c203ebdc330b3d70c126f9 changes precisely three proof fragments. Injectivity now applies congrArg to the same quotientEquiv followed by Multiplicative.toAdd, so parity_word and native toAdd_ofAdd yield an equality in the original V carrier. every_class retains the exact original witness and closes its tag endpoint with ofAdd_toAdd. inertia_classes_injective explicitly beta-normalizes the same two quotient-map applications before using the same inertia_class equalities and existing five-label injectivity.

Pinned TypeTags/Basic.lean blob 84f5742d2b2ffb18363c0e5c9c1d40d616bb9061 supplies both global tag identities as rfl. The exact own character-r14 and trace-r14 logs show the corresponding three errors. Both artifact digests, ZIP members, own RESULTs and predecessor intakes were independently verified.

The quotient remains the full positiveNormalizer modulo the kernel of its ACTUAL parity homomorphism. quotientEquiv, its original ordered-word right inverse, all sixteen labels, all five actual inertia representatives, quaternion product order, positive norm/order conditions and every original public statement remain unchanged. No identification of this kernel with rational scalars times integral units, nor a geometric deck action, is silently claimed. Same-module original_five_classes_injective and inertia_classes_injective are the actual consumers. A repeated read-only scan found no external qualified use in either full character/trace root closure; import-only PELPrimeRightLattice318 is not presented as a mathematical consumer.

## Contract and provenance

The freshly supplied OTHER-APPLICATION.md, SHA 9a7fac63c1cfc3a17e7cb024be6785ccbd5b022c2b1a8931de4c2f963a4691b9, gives nine substantive obligations for each source. Its original inputs, constructed objects, full coverage, transition orientations, identity/scalar/sign details, exceptional cases and actual consumer limitations agree with the inspected sources. Its source-only and failed-module caveats are retained.

The checker matched published f89bd0a3 before bytes and their unchanged copies at geometry-only tip 83851e60, authentic three own failures, native API blobs, source imports/options/public headers, unchanged Siegel suffix and exact quotient delta. No Lean was run; no compiler, kernel, recursive-axiom, full-packet or independent mathematical acceptance is asserted. Final packaging must bind these exact bytes and keep observed frontier evidence distinct from inherited unresolved modules.
