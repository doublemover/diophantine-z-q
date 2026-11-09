# Application contract: actual affine comparison coherence

Draft only. Exact source and document bindings are in APPLICATION.json. This
packet does not change accepted sources or the historical audit register.

1. **Required inputs.** The accepted TildePullback318 comparison is defined by
   left-adjoint uniqueness after transporting the actual sheaf pullback right
   adjoint along globalNatIso. Conjugation takes a natural map from the second
   left adjoint to the first and produces the reverse map of right adjoints.
   The generic proof checks the exact unit transpose before identifying a mate.
2. **Constructed objects.** The sheaf maps are original Scheme.Modules pullback,
   pushforward, composition, identity and equality comparisons. Spec.map_comp
   and Spec.map_id are retained explicitly. Scalar maps are the original
   ModuleCat extension/restriction comparisons, not substitute tensor maps.
3. **Coverage.** R, S and T are arbitrary commutative rings and the morphisms
   are arbitrary ring morphisms. Composition and identity are equalities of
   natural transformations on every module. No field, reducedness, generic
   point, finite-type or flatness hypothesis is imposed.
4. **Transition directions.** TildePullback318.pullbackIso maps pullback of
   tilde to tilde of scalar extension. Its mate is globalNatIso.inv. The inverse
   sheaf composition comparison has forward pushforward composition as mate;
   the scalar composition forward map has inverse scalar restriction as mate.
   Every associator in the two pasted paths is retained in the formal statement.
5. **Hypothesis checks.** The generic conjugation lemma derives the exact mate
   from the original adjunction unit equation. No composition or identity
   coherence is a premise. The global comparison equations are checked on
   actual sections, where equality-transport restrictions reduce to identity.
6. **Consumer identity.** The concluding component equalities explicitly mention
   TildePullback318.pullbackIso, Scheme.Modules canonical composition/identity
   via named Spec transports, and ModuleCat.extendScalarsComp/extendScalarsId.
   Thus the downstream line sections comparison can consume these original
   maps without choosing a new isomorphism or correcting it by an automorphism.
7. **Scalars and normalization.** All scalar actions remain in ModuleCat object
   types, even where the underlying additive map is identity. Composition is
   fixed by actual adjunction mates, not by equality of isomorphism classes.
   No scalar, norm, degree, polarization or coefficient is suppressed.
8. **Downstream boundary.** These are canonical comparison coherence equations.
   Applying them to the original line sectionsIso and transporting the geometric
   diagonal/triple equations remains separate. Effective affine descent from
   geometric data, arbitrary-scheme gluing, rigidification gluing, degree zero
   and representability are not claimed, and no arithmetic premise is replaced.
9. **Evidence and acceptance.** Five new modules import only the accepted
   baseline and pinned upstream APIs. Static hash/import/placeholder validation
   passes; no local Lean ran. Hosted strict checking, recursive axiom auditing
   and independent acceptance are pending. This contract grants no acceptance.
