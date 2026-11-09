# Exact primary API declarations read

Mathlib commit:56a005855ea17e0b0958f73ec801ae140b0a1679.
Read through the GitHub file connector at this exact ref, not default-branch search snippets.

Mathlib/Algebra/Homology/DerivedCategory/Ext/ExtClass.lean:

```lean
lemma extClass_naturality {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    h₁.extClass.comp (Ext.mk₀ f.τ₁) (add_zero 1) =
      (Ext.mk₀ f.τ₃).comp h₂.extClass (zero_add 1) := by
  let := HasDerivedCategory.standard C
  ext
  simpa [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using! (singleTriangle.map h₁ h₂ f).comm₃
```

Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean:

```lean
noncomputable def δ :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))
```

This ACTUAL site Mayer-Vietoris delta has no additional sign. The differently
named general Ext.δ in ExactSequences.lean has a sign normalization and is NOT
the producer consumed by OpenMayerVietoris318.boundary. The new coefficient is
therefore restriction(a_i)-restriction(a_j). The exact short-complex map and
extClass_naturality, rather than a naming convention, prove the consumed sign.

The same pinned ExactSequences.lean covariant_sequence_exact₁ and
covariant_sequence_exact₃ supply surjectivity and the section-image kernel of
the actual injective presentation. The existing original
AffineOpenSectionLifting318.surjective_affine_all supplies every affine local
lift, including the empty-open case. Topology/Sheaves/AddCommGrpCat.lean
Sheaf.sections_exact_of_left_exact supplies unique original structure-sheaf
coefficients, using the original inclusion mono for uniqueness.
