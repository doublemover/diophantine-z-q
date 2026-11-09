# Application contract: full affine-basis morphism extension

1. **Source requirements.** Mathlib TopCat.Sheaf.restrictHomEquivHom requires a genuine topology basis and an actual sheaf target. Scheme.isBasis_affineOpens supplies the whole original affine-open basis. Scheme.Modules.isSheaf supplies the original target sheaf law. No derived descent or unspecified stack theorem is used. Mathlib source is pinned at56a005855ea17e0b0958f73ec801ae140b0a1679, including Topology/Sheaves/SheafCondition/Sites.lean.

2. **Constructed objects.** For original Scheme module sheaves M,N, Data contains linear maps Γ(M,U)→Γ(N,U) over the original Γ(X,U) for every actual affine open U, natural under original nested-open restrictions. basisMap is an actual additive natural transformation on the induced affine-open indexing category. additiveMap is the original basis-extension equivalence applied to that transformation. hom is a genuine M→N with those exact sections.

3. **Coverage.** The indexing set is all X.affineOpens, not principal opens or a selected finite cover. basis_range proves its image is the original affine-open set. Every point of every open has an affine neighborhood inside that open, via Scheme.isBasis_affineOpens. This supplies section separation on arbitrary opens, including non-affine intersections. No assumption that affine intersections remain affine is made.

4. **Transition directions.** Data.natural has the original restriction map on source and target, from the larger affine open to the smaller one. The basis extension is from those original local components to the global sheaf map. The recovered affine component equality follows from the actual inverse law of the same basis-extension equivalence. Backward iso maps are exact linear-equivalence inverses, with naturality derived from the forward square.

5. **Hypothesis checks.** Global additive naturality comes from the basis-extension functor. Global scalar linearity is proved by restricting to all affine neighborhoods, using the original M.val.map_smul and N.val.map_smul and supplied affine linearity. No global linearity or non-affine component map is an input. Original sheaf morphisms are shown equal from affine component equality by actual sheaf separation and their original naturality.

6. **Consumer identity.** hom_affine recovers the original supplied linear map at every actual affine open. hom_unique identifies the constructed global map with any original sheaf map having those same components. IsoData reconstructs an actual original M≅N, not an isomorphism class or a separate sheafification. hom_cocycle proves equality of original whole-sheaf composites from exact affine component equations.

7. **Scalars and normalization.** All maps are linear over the original open's section ring, with its original semilinear restriction action. No scalars are rescaled and no coefficient ring is replaced. The ordinary additive basis-extension equivalence is upgraded to the actual module-sheaf map only after proving all-open scalar linearity.

8. **Downstream boundary.** This general mechanism is suitable for constructing maps across non-affine chart intersections. Connecting it to the actual original chart restrictions and their affine component comparisons remains the next explicit adapter; its existence is not treated as an input already discharged. Global effective descent, arbitrary non-affine fppf source and represented Picard/Jacobian remain separate. No full318/326 theorem or baseline admission is claimed.

9. **Evidence and acceptance.** The96 predecessor sources are copied byte-for-byte from affine-open-chart-coherence-r2. The two new sources, current application and exact dependency closure are hash bound. Static placeholder/import/hash checks and the audit-history self-test are not elaboration or acceptance. No local Lean was run. Hosted compilation, recursive axiom audit and independent acceptance remain pending; no independent approval is manufactured.

## Revision after bounded source review

Remove the redundant rfl after all three exact affine-component rewrites in hom_comp. The final equality is definitional and the rewrite tactic may already discharge it. No theorem or construction changes. Hosted validation remains pending.
