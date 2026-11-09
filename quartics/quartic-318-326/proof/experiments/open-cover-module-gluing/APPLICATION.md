# Application contract: matching-family object gluing

1. **Source requirements.** ModuleLocalGluing318.res and res_res are the original
   restriction maps and their composition. TopCat.Sheaf.existsUnique_gluing' and
   eq_of_locally_eq' require actual open covers, compatible original sections and
   the sheaf property of the original local module. The unique-gluing criterion
   gives the actual sheaf condition. PresheafOfModules.ofPresheaf requires genuine
   semilinear restriction; isoMk requires linear components natural on all opens.
   The original overEquiv and overFunctorEquiv identify actual site-over-open
   modules with actual open-subscheme restrictions. These interfaces are read
   at pinned Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.

2. **Constructed objects.** Data U M consists of actual ambient module sheaves,
   every pairwise common-subopen linear transition, and actual naturality,
   identity and cocycle laws. sections W is the submodule of original local
   section families satisfying all transitions. Restrictions, the module
   presheaf, component gluings, the global sheaf, recovered chart isomorphisms
   and the final covered framed line are constructed explicitly in the five
   source files. No object gluing result is an input.

3. **Coverage.** All chart indices, all pairs and triples, every ambient open
   and every common subopen are quantified. Component sheaf gluing uses the
   actual cover V k intersect U i of W intersect U i, with coverage proved from
   the supplied original V cover. The final line requires top ≤ supremum U;
   no arbitrary family is treated as a cover. Empty charts and overlaps are
   retained, and the sheaf construction does not require a finite cover.

4. **Transition directions.** transition i j maps original sections of M i to
   original sections of M j. Matching families satisfy transition i j applied
   to restricted i component equals restricted j component. fromChart extends
   a section through these same transitions; evaluate recovers the i component.
   Actual chartIso maps the glued restriction to the original M i restriction.
   The final frame is the original local frame followed by chartIso inverse.

5. **Hypothesis checks.** Matching families form a submodule because original
   restrictions are semilinear and transitions are linear over the same section
   ring. Functorial restrictions use res_res. Chart recovery uses original
   identity/cocycle and naturality laws. Componentwise gluing uses the sheaf law
   of M i; transition compatibility is checked by local equality on every
   covering subopen. The resulting matching-family sheaf law is proved by
   existence and uniqueness, not assumed. Rank-one frames are genuine supplied
   sheaf isomorphisms, and coverage is checked separately.

6. **Consumer identity.** The global sheaf has exactly sections W as its original
   section module, not an untracked sheafification. chartLinearEquiv has evaluate
   as its forward map and fromChart as inverse. overIso uses those same natural
   components; chartIso uses exactly the original overFunctorEquiv. The line
   object's sheaf is literally the constructed sheaf, with the original U cover
   and original frames transported through those same chart comparisons.

7. **Scalars and normalization.** Each component retains restriction of the
   actual Γ(X,W) action to Γ(X,W intersect U i). The matching submodule, every
   presheaf restriction and every chart equivalence have their scalar laws
   proved. The original structure-sheaf restriction composes without a scalar
   correction. No field, rationalization, chosen unit or rank-only substitute
   replaces the original coefficients or transitions.

8. **Downstream boundary.** This provides actual arbitrary-scheme module
   object gluing from the stated all-subopen data and a global line from actual
   covering frames. It does not yet convert arbitrary chart sheaves/direct-image
   transitions to this input, construct refinements of local line frames, or
   prove the changing-base-chart compatibility of affine reconstruction.
   Those are required to apply this construction to the original fppf datum.
   Full Picard/Jacobian representability and arithmetic completeness remain
   separate; existing accepted/frozen sources are unchanged.

9. **Evidence and acceptance.** The five complete sources, all direct baseline
   imports and all nine obligations are bound in intake.json/APPLICATION.json.
   Source/hash/import/placeholder validation and audit-history self-tests are
   structural checks only. No local Lean ran. Hosted replay, recursive axiom
   audit and independent acceptance are pending; no approval record or theorem
   completeness claim is manufactured.
