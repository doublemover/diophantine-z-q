# Application contract: unique original geometric morphism descent

Draft only. Exact sources and documents are bound in APPLICATION.json.

1. **Required inputs.** The actual faithfully flat module equivalence needs
   coalgebra-compatible maps. The new input is an actual morphism between
   original covering sheaves, commuting with their actual geometric overlap
   maps. The exact module/coaction compatibility is derived before applying
   the inverse equivalence. The two original geometric diagonal/triple laws
   are inherited from the explicit geometric data, not replaced by coalgebras.
2. **Constructed objects.** Datum contains the unchanged original Line on
   Spec S, its sheaf overlap morphism and its geometric laws. Hom contains the
   actual covering sheaf map and its original overlap square. Its coalgebra
   morphism has f exactly moduleSpecΓFunctor.map of that sheaf map. The base
   module morphism is the actual inverse-equivalence functor image; the base
   sheaf morphism is its actual tilde image between the original reconstructed
   line objects.
3. **Coverage.** The rings are arbitrary commutative rings with the given
   faithfully flat algebra structure. The proofs apply to all compatible
   sheaf maps, not just isomorphisms, scalars or generic-point maps. Pullback
   faithfulness is proved for every morphism between affine tilde objects.
   No reducedness, field or finite-type restriction is introduced.
4. **Transition directions.** The covering overlap square is overlapD then
   second-pullback of h equals first-pullback of h then overlapE. This gives
   coactionD then original comonad.map of Gamma(h) equals Gamma(h) then
   coactionE. The final square is pullback(descended h) then comparisonE equals
   comparisonD then h. Actual inverse pairs and12-then23-equals13 cocycles
   descend in those same directions.
5. **Hypothesis checks.** Original section-comparison naturality at both
   overlap endpoints gives the module square. The original affine tensor
   comparison's naturality and actual extension adjunction give the coaction
   square. Inverse-equivalence counit naturality yields the module comparison
   square, then original tilde comparison/counit naturality yields the sheaf
   square. Faithful flatness supplies actual comonadicity, not an extra assumed
   faithfulness or uniqueness hypothesis.
6. **Consumer identity.** The descended line and its comparison are precisely
   OriginalGeometricAffineLine318.line and pullbackIso. comparison_hom exposes
   that exact original map through the same descended moduleIso and original
   line counit. exists_unique_map quantifies over every actual sheaf map
   between these same base line objects, proving uniqueness with the exact
   original comparison square. No different module or line is substituted.
7. **Scalars and normalization.** All original scalar actions, extension and
   restriction functors, sheaf pullbacks, tilde functors and counits remain.
   No scalar automorphism is chosen to repair a square. Morphism equality and
   inverse/cocycle identities are literal equalities, not equalities of classes
   or unspecified isomorphisms. No arithmetic coefficient or exception changes.
8. **Downstream boundary.** These are unique affine transition maps over one
   fixed faithfully flat ring extension. Reconstruction compatibility across
   distinct base charts, arbitrary scheme-cover gluing, the general scheme
   fiber-product descent category, and rigidification gluing remain open.
   Picard associated-sheaf identification, degree zero, representability and
   the full arithmetic theorem are not claimed. No historical arithmetic
   premise is changed by these application contracts.
9. **Evidence and acceptance.** Five new sources,32 byte-identical producer and4 repaired producer
   copies are bound. The predecessor's full hosted acceptance remains pending.
   Static checks pass, no local Lean ran, and complete41-source hosted strict
   replay, recursive audit and independent acceptance remain pending. This
   contract is not independent approval or a proof certificate.

## Exact hosted repairs folded into this superset

Run42577530786 at e3a0ead passed the first14 scalar/coassociativity producers
(including the previous scalar-composition repair), then found missing local
R-module instances in triple coordinate expressions. The coordinate source and
its two immediate tensor-formula consumers now use only canonical restriction
through algebraMap R S and its scalar tower. The tilde packet passed its global
section coherence source, then needed NatTrans.id_app explicitly reduced before
Category.comp_id in the finite mate proof. These four repairs preserve all
mathematical statements and actual maps. Exact logs/RESULTs are retained here;
committed predecessor packets, including the36-source packet, remain unchanged.
