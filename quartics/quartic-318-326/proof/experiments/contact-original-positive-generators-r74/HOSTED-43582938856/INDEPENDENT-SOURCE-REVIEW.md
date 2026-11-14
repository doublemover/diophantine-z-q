# Independent arithmetic positive source review
Reviewer: lean_review_resume; internal source comparison, not whole-proof acceptance.

## Frozen evidence and route
Proof run43582938856, head6fe85071934d36d22cfdbd7c503f6b9a54e6ef18, artifact14109189107. Exact source beforebb1851560b4cdbac3393982f06bba27fc2149d867c55b131d6cc3cb3c48fd860; final after6d87e7627a950181360f92ad9c710c2ea966af8c742792c8c6aa871f24da2ac5. Human contract d54e6b5ef5f0bbd48dcde273270065e5c41b2b84ac0b9526efa2da4cefd14152 was read with the actual source/producers/consumers. The preliminary d305aa source and prior contract are preserved, not silently relabeled.

I independently matched own GitHub artifact/head/digest, ZIP progress-experiments RESULT/log, published intake and before bytes. Quotient passed28.882s; RationalCohomology failed14.499s. Hard failures include exported cohomology_smul reduction and two local registrations unable to infer p, followed by boundaryLinear cascades. Reducibility warnings are not additional hard errors. Later bbda diagnostic changes do not alter any production experiment bytes; no result from that run is substituted.

## Required input, constructed input and exact identity
For every original scheme X, p:X→Specℚ and original line L, scalar p U is the unchanged structure-map ring homomorphism on U. sectionModule is literally Module.compHom along that scalar on the SAME section carrier. multiply is unchanged global ModuleScalar multiplication forgotten to the SAME additive sheaf, with scalar_restrict providing the original open-wise action. No choice of coordinates, quotient or abstract replacement constructs the module.

cohomologyModule is the original CohomologyRationalScalar.ofAction on actual Sheaf.H(additive L)n, with action Sheaf.H.map(multiply p L a)n. I read ofAction's full zero/one/add/multiplication laws; multiply_mul retains composition b≫a in the orientation consumed by its covariant cohomology law. The same n, a, x and every degree remain covered.

The two constructors gain expose/reducible, matching the read original ofAction convention, without body changes. Invalid uninferable local registrations are removed. boundaryLinear's RESULT TYPE and body install precisely sectionModule p L(U∩V) and cohomologyModule p L1. This retains p in the intended linear-map type; it is not a caller-supplied new class or implicit change of rational action.

I independently fetched pinned Mathlib Algebra/Module/LinearMap/Rat.lean blob12ff091a5dd2450f2119bef24c63943dc55ceb93. Its exposed toRatLinearMap needs additive groups with the chosen rational modules, and keeps the exact additive homomorphism while proving map_rat_smul. Its coe lemma is rfl. Thus the constructed linear map's function remains the ORIGINAL derived Mayer–Vietoris boundary, not a coordinate map.

boundary_scalar installs those SAME two fixed-p instances and consumes boundaryLinear.map_smul. Source rational multiplication reduces to scalar p(U∩V)a acting on the original section; target multiplication reduces to Sheaf.H.map(multiply p L a)1. Final boundaryLinear exposure is a supporting reduction boundary because that proof must identify its underlying map with the displayed original boundary. It is not falsely called a separate observed error. The public proposition remains unchanged; boundaryLinear result type intentionally acquires letI scopes.

## Domain, consumers and conventions
Boundary results retain IsIntegral X, ALL U,V with U∨V=top and ALL overlap sections. There is no new affine, nonempty, injectivity, triviality or nonzero premise. All degrees for cohomologyModule and all rational scalars remain. No norm, trace factor or sign is introduced.

Immediate consumers are cohomology_smul and boundary_scalar. I read actual external ContactOriginalCohomologyCoordinates degree-one module, ContactOriginalLineCohomologyFinite degree-zero module and ContactOriginalLineSectionsFinite top-section module: each supplies the original ContactIntrinsicDifferentials.structureMap c. ContactOriginalCohomologyCoordinates has its own coordinate boundaryLinear; it is not misrepresented as a direct use of this candidate's boundaryLinear. Consumer copies were independently matched to published Git bytes.

## Disposition
The human contract's domains, original actions, explicit constructor/function identities, changed type scopes, supporting exposure and consumer limitations are source-supported. No imports/resource/trust lines change; existing caps are not newly endorsed. No Lean/Lake, kernel/recursive axiom audit or full theorem acceptance occurred. Suitable for exact-copy draft propagation and hosted testing; application success and downstream modules remain unverified. New packet-specific nine-obligation contracts and propagation still require separate review.
