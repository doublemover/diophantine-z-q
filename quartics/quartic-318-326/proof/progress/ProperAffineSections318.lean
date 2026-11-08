module
public import ProperGlobalSections318
public import StructurePushforwardSplit318
public section
noncomputable section
namespace ProperAffineSections318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Universally closed morphisms induce integral maps on every affine base open. -/
theorem app_integral (p : X ⟶ Y) [UniversallyClosed p]
    (U : Y.Opens) (hU : IsAffineOpen U) : (p.app U).hom.IsIntegral := by
  letI : IsAffine U := hU
  have h := isIntegral_appTop_of_universallyClosed (p ∣_ U)
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.isIntegral_respectsIso.cancel_right_isIso] at h
  convert! h using 1
  exact Iff.of_eq (congrArg (fun V : Y.Opens => (p.app V).hom.IsIntegral) U.ι_image_top.symm)

/-- The actual section gives a ring retraction on every base open. -/
theorem section_app_split (p : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (U : Y.Opens) : ∃ g : Γ(X, p ⁻¹ᵁ U) →+* Γ(Y, U),
      g.comp (p.app U).hom = RingHom.id _ := by
  have hpre : U ≤ e ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, he, Scheme.Hom.id_preimage]
  let g := e.appLE (p ⁻¹ᵁ U) U hpre
  refine ⟨g.hom, ?_⟩
  have h : p.app U ≫ g = 𝟙 _ := by
    dsimp only [g]
    rw [p.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have hident (f : Y ⟶ Y) (hf : f = 𝟙 Y) (h : U ≤ f ⁻¹ᵁ U) :
        f.appLE U U h = 𝟙 _ := by
      subst f
      simp [Scheme.Hom.appLE]
      exact Y.presheaf.map_id _
    exact hident _ he _
  exact congrArg CommRingCat.Hom.hom h

/-- Integral source and an actual section force equality of functions on affine
base opens. Empty opens are handled separately. -/
theorem app_bijective [IsIntegral X] (p : X ⟶ Y) [UniversallyClosed p]
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y) (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Bijective (p.app U) := by
  classical
  by_cases hne : Nonempty U
  · letI := hne
    let y : U := Classical.choice hne
    have hp : p (e y) ∈ U := by
      change (e ≫ p) y ∈ U
      rw [he]
      exact y.property
    letI : Nonempty (p ⁻¹ᵁ U) := ⟨⟨e y, hp⟩⟩
    obtain ⟨g, hg⟩ := section_app_split p e he U
    exact IntegralRetraction318.bijective (p.app U).hom g (app_integral p U hU) hg
  · have hbot : U = ⊥ := by
      apply le_antisymm _ bot_le
      intro y hy
      exact (hne ⟨⟨y, hy⟩⟩).elim
    subst U
    haveI : Subsingleton Γ(X, p ⁻¹ᵁ ⊥) := by simp only [Scheme.Hom.preimage_bot]; infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- The actual structure-sheaf morphism is an isomorphism, detected on the
full affine basis. This is not merely an equality of global sections. -/
theorem unitMap_isIso [IsIntegral X] (p : X ⟶ Y) [UniversallyClosed p]
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y) :
    IsIso (StructurePushforwardSplit318.unitMap p) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hi : IsIso (F.map (StructurePushforwardSplit318.unitMap p)) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : Y.affineOpens => U.1)
    · convert! Y.isBasis_affineOpens using 1
      exact Subtype.range_coe_subtype
    · intro U
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact app_bijective p e he U.1 U.2
  letI := hi
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  exact (inferInstance : IsIso ((F.map (StructurePushforwardSplit318.unitMap p)).hom.app (.op U)))

variable {R : Type u} [CommRing R] [IsDomain R]
/-- Over every domain base the actual completed Weierstrass family has
π_*O = O via its canonical structural map and infinity section. -/
theorem family_unitMap_isIso (A B : R) :
    IsIso (StructurePushforwardSplit318.unitMap (WeierstrassGluing318.structureMap A B)) := by
  letI := CompletedIntegral318.completed_integral A B
  letI := CubicClosedImmersion318.structure_proper A B
  exact unitMap_isIso _ _ (WeierstrassGluing318.infinity_section A B)
end ProperAffineSections318
