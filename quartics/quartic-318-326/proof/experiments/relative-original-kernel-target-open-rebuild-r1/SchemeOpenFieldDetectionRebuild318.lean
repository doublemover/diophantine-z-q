module
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace SchemeOpenFieldDetectionRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y T : Scheme.{u}}
lemma factor_iff_range (U : Y.Opens) (f : T ⟶ Y) :
    (∃ g : T ⟶ U.toScheme, g ≫ U.ι=f) ↔ Set.range f ⊆ (U : Set Y) := by
  constructor
  · rintro ⟨g,rfl⟩
    rintro _ ⟨x,rfl⟩
    exact (g x).property
  · intro h
    have h' : Set.range f ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
    exact ⟨IsOpenImmersion.lift U.ι f h',IsOpenImmersion.lift_fac _ _ _⟩
lemma preimage_factor (U : Y.Opens) (f : X ⟶ Y) (g : T ⟶ X) :
    (∃ a : T ⟶ (f ⁻¹ᵁ U).toScheme, a ≫ (f ⁻¹ᵁ U).ι=g) ↔
      ∃ b : T ⟶ U.toScheme, b ≫ U.ι=g ≫ f := by
  rw [factor_iff_range,factor_iff_range]
  constructor
  · intro h
    rintro _ ⟨t,rfl⟩
    exact h ⟨t,rfl⟩
  · intro h
    rintro _ ⟨t,rfl⟩
    exact h ⟨t,rfl⟩
/-- Open equality uses ALL native residue fields, not just ground-field
rational points. This theorem makes no reducedness assumption. -/
lemma ext_fields (U V : X.Opens)
    (h : ∀ (K : CommRingCat.{u}) [Field K] (f : Spec K ⟶ X),
      (∃ a : Spec K ⟶ U.toScheme, a ≫ U.ι=f) ↔
        ∃ b : Spec K ⟶ V.toScheme, b ≫ V.ι=f) : U=V := by
  ext x
  have hx (W : X.Opens) : (∃ a : Spec (X.residueField x) ⟶ W.toScheme,
      a ≫ W.ι=X.fromSpecResidueField x) ↔ x ∈ W := by
    rw [factor_iff_range,Scheme.range_fromSpecResidueField,Set.singleton_subset_iff]
  exact (hx U).symm.trans ((h (X.residueField x) (X.fromSpecResidueField x)).trans (hx V))
end SchemeOpenFieldDetectionRebuild318
