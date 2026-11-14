# Bounded original tensor-chart restriction repair

Exact hosted run 43519890754 at 58753ec5f3b41268c5ceedae5264593b4f2aa0de, positive packet r65, artifact 14081609906. The predecessor module hash is recorded in MANIFEST.json. No local Lean or Lake execution, resource-budget change, external statement change, scalar-map change, or claim of kernel success accompanies this draft.

## Observed frontier

ContactOriginalRestrictionCoordinates318 passed in 123.832 seconds. The next four modules also passed: OriginalOpenLineRestrictionUnit318, OriginalOpenPullbackSections318, ContactWholeOpenSectionRestriction318 and OriginalPullbackSectionComposition318. OriginalTensorChartWholeRestriction318 is the first failing module. Raw RESULT.json and diagnostics are preserved in evidence/.

## Exact correction

At chart_unit and recovered_unit, evaluating e.hom_inv_id yields a ConcreteCategory.hom applied to a composition or identity of section maps. Scheme.Modules.Hom.comp_app and id_app expose those categorical maps, but the ModuleCat-specific application lemmas do not match the generic ConcreteCategory.hom representation. The hosted linter marks both arguments unused at both locations. Replace only these four names by ConcreteCategory.comp_apply and ConcreteCategory.id_apply. Their pinned primary statements rewrite exactly `(hom (f ≫ g)) x` to `(hom g) ((hom f) x)` and `(hom (𝟙 _)) x` to x.

The first cancellation still uses the original e : pullback j L.object ≅ M at the actual sectionPull j L.object s. The second still uses the original chartComparison at the actual sectionPull i.hom M (e.hom.app top (sectionPull j L.object s)). These are evaluations of their hom_inv_id equalities, not newly chosen inverses. The unchanged naturality and recovery_apply consumers receive the same original section.

At chartRecovery_apply, the unqualified Functor.map_id resolves to the unrelated functional-functor law with pattern `fun x => id <$> x`, as shown literally by the diagnostic. Qualify it as CategoryTheory.Functor.map_id. The pinned categorical source states F.map (𝟙 X) = 𝟙 (F.obj X). This removes only the identity restriction at the same full-image open; no change of ambient open, pullback, pushforward or displayed path is made.

## Application-domain and consumer checks

The source retains arbitrary CommRingCat R,A,B with both original Algebra instances, original X, p,j, original scheme isomorphism i, hbase and hchart, original line L, original M and comparison e. All universe binders and all sections s or t remain unchanged. There is no finite-index restriction, exceptional-case omission or coefficient-field substitution. In the final original_restriction theorem, chartRecovery_apply and recovered_unit still produce exactly e.hom.app top (sectionPull j L.object s). No rank-based surrogate comparison or unrelated global-section equivalence is introduced. All downstream theorem statements and proof consumers are unchanged.

## Limits

The hosted log also reports implicit-transparency type-checking notes involving preimage-of-top and the pushforward section carrier. The minimal candidate repairs the three directly observed mismatched rewrite patterns; it does not claim these ancillary transparency notes are independently eliminated. Fresh hosted Lean is required to establish elaboration and recursive axiom checking. Distinct internal source review is pending and is not whole-proof mathematical acceptance.
