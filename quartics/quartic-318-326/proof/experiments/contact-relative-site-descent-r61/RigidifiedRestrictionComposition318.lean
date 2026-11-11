module
public import RigidifiedOpenRestriction318
public section
noncomputable section
namespace RigidifiedRestrictionComposition318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  (e₀ : S₀ ⟶ X₀) (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂)
  (a₁ : X₁ ⟶ X₀) (a₂ : X₂ ⟶ X₁) (a₀₂ : X₂ ⟶ X₀)
  [IsOpenImmersion a₁] [IsOpenImmersion a₂] [IsOpenImmersion a₀₂]
  (b₁ : S₁ ⟶ S₀) (b₂ : S₂ ⟶ S₁) (b₀₂ : S₂ ⟶ S₀)
  (h₁ : e₁ ≫ a₁ = b₁ ≫ e₀) (h₂ : e₂ ≫ a₂ = b₂ ≫ e₁)
  (h₀₂ : e₂ ≫ a₀₂ = b₀₂ ≫ e₀) (ha : a₂ ≫ a₁ = a₀₂) (hb : b₂ ≫ b₁ = b₀₂)
  (L : RigidifiedLine e₀)

/-- A compatible composition path built entirely from the original
restriction/pullback comparisons and original pointed composition. -/
@[expose] def path : CompatibleIso e₂
    (RigidifiedOpenRestriction318.line e₁ e₂ a₂ b₂ h₂
      (RigidifiedOpenRestriction318.line e₀ e₁ a₁ b₁ h₁ L))
    (RigidifiedOpenRestriction318.line e₀ e₂ a₀₂ b₀₂ h₀₂ L) :=
  RigidifiedIsoCoherence318.compose e₂
    (RigidifiedOpenRestriction318.comparison e₁ e₂ a₂ b₂ h₂
      (RigidifiedOpenRestriction318.line e₀ e₁ a₁ b₁ h₁ L))
    (RigidifiedIsoCoherence318.compose e₂
      (RigidifiedPointedPullback318.mapIso e₁ e₂ a₂ b₂ h₂
        (RigidifiedOpenRestriction318.comparison e₀ e₁ a₁ b₁ h₁ L))
      (RigidifiedIsoCoherence318.compose e₂
        (RigidifiedCanonicalComposition318.compositionAlong e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂
          a₀₂ b₀₂ ha hb h₀₂ L)
        (RigidifiedIsoCoherence318.inverse e₂
          (RigidifiedOpenRestriction318.comparison e₀ e₂ a₀₂ b₀₂ h₀₂ L))))

/-- This is exactly the original restriction collapse used by Fi-only
open gluing, including its original restriction equality transport. -/
lemma path_hom :
    (path e₀ e₁ e₂ a₁ a₂ a₀₂ b₁ b₂ b₀₂ h₁ h₂ h₀₂ ha hb L).iso.hom =
      (RestrictionTransitionPasting318.collapse a₂ a₁ a₀₂ ha).hom.app L.line.object := by
  have hp := RigidifiedCanonicalComposition318.compositionAlong_hom
    e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂ a₀₂ b₀₂ ha hb h₀₂ L
  have hn := (Scheme.Modules.restrictFunctorIsoPullback a₂).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback a₁).hom.app L.line.object)
  change (Scheme.Modules.restrictFunctorIsoPullback a₂).hom.app
      ((Scheme.Modules.restrictFunctor a₁).obj L.line.object) ≫
      (Scheme.Modules.pullback a₂).map ((Scheme.Modules.restrictFunctorIsoPullback a₁).hom.app L.line.object) ≫
      (RigidifiedCanonicalComposition318.compositionAlong e₀ e₁ e₂ a₁ a₂ b₁ b₂ h₁ h₂
        a₀₂ b₀₂ ha hb h₀₂ L).iso.hom ≫
      (Scheme.Modules.restrictFunctorIsoPullback a₀₂).inv.app L.line.object = _
  rw [hp]
  apply (cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback a₀₂).hom.app L.line.object)).mp
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
  rw [← Category.assoc,← hn,Category.assoc]
  exact RestrictionTransitionPasting318.comparison_path a₂ a₁ a₀₂ ha L.line.object
end RigidifiedRestrictionComposition318
