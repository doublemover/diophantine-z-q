module
public import ClutchedModule318
public section
noncomputable section
namespace ClutchedModuleFrames318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ClutchedModule318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y₀ Y₁ W : Scheme.{u}}
    (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion k₀] [IsOpenImmersion k₁]

/-- On the other member of a full two-chart intersection, restriction of the
pushed-forward structure sheaf is an isomorphism on every subopen. -/
theorem restriction_isIso
    (hr : j₁⁻¹ᵁ j₀.opensRange=k₁.opensRange) :
    IsIso ((Scheme.Modules.restrictFunctor j₀).map (restriction j₁ k₁)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun x : Γ(Y₁,j₁⁻¹ᵁ(j₀ ''ᵁ U)) =>
    (restriction j₁ k₁).app (j₀ ''ᵁ U) x)
  simp only [restriction_app]
  have hv : j₁⁻¹ᵁ(j₀ ''ᵁ U) ≤ k₁.opensRange := by
    rw [←hr,←Scheme.Hom.image_top_eq_opensRange]
    exact j₁.preimage_mono (j₀.image_mono le_top)
  letI := k₁.isIso_app _ hv
  exact ConcreteCategory.bijective_of_isIso (k₁.app (j₁⁻¹ᵁ(j₀ ''ᵁ U)))

variable (h : k₁≫j₁=k₀≫j₀) (a : Γ(W,⊤)) (ha : IsUnit a)
    (hr₀ : j₀⁻¹ᵁ j₁.opensRange=k₀.opensRange)
    (hr₁ : j₁⁻¹ᵁ j₀.opensRange=k₁.opensRange)

instance toPresheafPreservesFiniteLimits (Z : Scheme.{u}) :
    PreservesFiniteLimits (Scheme.Modules.toPresheaf Z) :=
  inferInstanceAs (PreservesFiniteLimits
    (SheafOfModules.toSheaf Z.ringCatSheaf ⋙ sheafToPresheaf _ _))

instance restrictionPreservesLimit {J : Type} [SmallCategory J] [FinCategory J] (F : J ⥤ X.Modules) :
    PreservesLimit F (Scheme.Modules.restrictFunctor j₀) := by
  haveI : PreservesLimit F (Scheme.Modules.restrictFunctor j₀ ⋙ Scheme.Modules.toPresheaf Y₀) := by
    apply preservesLimit_of_evaluation
    intro U
    change PreservesLimit F (Scheme.Modules.toPresheaf X ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat).obj (Opposite.op (j₀ ''ᵁ U.unop)))
    haveI : PreservesLimit F (Scheme.Modules.toPresheaf X) := inferInstance
    haveI : PreservesLimit (F ⋙ Scheme.Modules.toPresheaf X)
        ((CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat).obj (Opposite.op (j₀ ''ᵁ U.unop))) :=
      by
        haveI : HasLimitsOfShape J AddCommGrpCat.{u} := inferInstance
        exact evaluation_preservesLimit (F ⋙ Scheme.Modules.toPresheaf X) _
    exact comp_preservesLimit _ _
  haveI : ReflectsLimit (F ⋙ Scheme.Modules.restrictFunctor j₀) (Scheme.Modules.toPresheaf Y₀) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact preservesLimit_of_reflects_of_preserves _ (Scheme.Modules.toPresheaf Y₀)

include ha hr₁ in
/-- The actual first local projection is an isomorphism after restriction. -/
theorem first_isIso :
    IsIso ((Scheme.Modules.restrictFunctor j₀).map (first j₀ j₁ k₀ k₁ h a)) := by
  letI := restriction_isIso j₀ j₁ k₁ hr₁
  letI := multiply_isIso a ha
  haveI : IsIso ((Scheme.Modules.restrictFunctor j₀).map
      (twistedRestriction j₀ j₁ k₀ k₁ h a)) := by
    unfold twistedRestriction
    rw [Functor.map_comp,Functor.map_comp]
    infer_instance
  have hp := (IsPullback.of_hasPullback (restriction j₀ k₀)
    (twistedRestriction j₀ j₁ k₀ k₁ h a)).map (Scheme.Modules.restrictFunctor j₀)
  exact hp.isIso_fst_of_isIso

include hr₀ in
/-- The actual second local projection is an isomorphism after restriction. -/
theorem second_isIso :
    IsIso ((Scheme.Modules.restrictFunctor j₁).map (second j₀ j₁ k₀ k₁ h a)) := by
  letI := restriction_isIso j₁ j₀ k₀ hr₀
  have hp := (IsPullback.of_hasPullback (restriction j₀ k₀)
    (twistedRestriction j₀ j₁ k₀ k₁ h a)).map (Scheme.Modules.restrictFunctor j₁)
  exact hp.isIso_snd_of_isIso

/-- A genuine local frame of the clutched module on the first whole chart. -/
@[expose] def firstFrame :
    (sheaf j₀ j₁ k₀ k₁ h a).restrict j₀ ≅ unit Y₀ := by
  letI := first_isIso j₀ j₁ k₀ k₁ h a ha hr₁
  exact asIso ((Scheme.Modules.restrictFunctor j₀).map (first j₀ j₁ k₀ k₁ h a)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j₀).app (unit Y₀)

/-- A genuine local frame of the clutched module on the second whole chart. -/
@[expose] def secondFrame :
    (sheaf j₀ j₁ k₀ k₁ h a).restrict j₁ ≅ unit Y₁ := by
  letI := second_isIso j₀ j₁ k₀ k₁ h a hr₀
  exact asIso ((Scheme.Modules.restrictFunctor j₁).map (second j₀ j₁ k₀ k₁ h a)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j₁).app (unit Y₁)
end ClutchedModuleFrames318
