module
public import ClutchedModule318
public import ModuleTopMorphisms318
public section
noncomputable section
namespace ClutchedModuleTop318
open AlgebraicGeometry CategoryTheory
open ClutchedModule318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y₀ Y₁ W : Scheme.{u}}
    (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
    (h : k₁≫j₁=k₀≫j₀) (a : Γ(W,⊤))
    (s₀ : Γ(Y₀,⊤)) (s₁ : Γ(Y₁,⊤)) (hs : k₀.appTop s₀=k₁.appTop s₁*a)

include hs in
theorem compatible_maps :
    ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₀).obj (unit Y₀)) s₀≫restriction j₀ k₀=
    ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₁).obj (unit Y₁)) s₁≫
      twistedRestriction j₀ j₁ k₀ k₁ h a := by
  rw [ModuleTopMorphisms318.ofTop_comp,ModuleTopMorphisms318.ofTop_comp]
  congr 1
  exact (show (restriction j₀ k₀).app ⊤ s₀=k₀.appTop s₀ from rfl).trans
    (hs.trans (twistedRestriction_top j₀ j₁ k₀ k₁ h a s₁).symm)

/-- A compatible pair of actual top-open regular functions produces a
morphism from the ambient unit sheaf to the clutched line. -/
@[expose] def map : unit X ⟶ sheaf j₀ j₁ k₀ k₁ h a :=
  lift j₀ j₁ k₀ k₁ h a
    (ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₀).obj (unit Y₀)) s₀)
    (ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₁).obj (unit Y₁)) s₁)
    (compatible_maps j₀ j₁ k₀ k₁ h a s₀ s₁ hs)

@[expose] def sectionTop : Γ(sheaf j₀ j₁ k₀ k₁ h a,⊤) :=
  (map j₀ j₁ k₀ k₁ h a s₀ s₁ hs).app ⊤ (show Γ(X,⊤) from 1)

theorem first_value :
    (first j₀ j₁ k₀ k₁ h a).app ⊤ (sectionTop j₀ j₁ k₀ k₁ h a s₀ s₁ hs)=s₀ := by
  have h := congrArg (fun f : unit X ⟶ (Scheme.Modules.pushforward j₀).obj (unit Y₀) =>
      f.app ⊤ (show Γ(X,⊤) from 1))
    (lift_first j₀ j₁ k₀ k₁ h a
      (ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₀).obj (unit Y₀)) s₀)
      (ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₁).obj (unit Y₁)) s₁)
      (compatible_maps j₀ j₁ k₀ k₁ h a s₀ s₁ hs))
  exact h.trans (ModuleTopMorphisms318.ofTop_top_one _)

theorem second_value :
    (second j₀ j₁ k₀ k₁ h a).app ⊤ (sectionTop j₀ j₁ k₀ k₁ h a s₀ s₁ hs)=s₁ := by
  have h := congrArg (fun f : unit X ⟶ (Scheme.Modules.pushforward j₁).obj (unit Y₁) =>
      f.app ⊤ (show Γ(X,⊤) from 1))
    (lift_second j₀ j₁ k₀ k₁ h a
      (ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₀).obj (unit Y₀)) s₀)
      (ModuleGlobalSections318.ofTop ((Scheme.Modules.pushforward j₁).obj (unit Y₁)) s₁)
      (compatible_maps j₀ j₁ k₀ k₁ h a s₀ s₁ hs))
  exact h.trans (ModuleTopMorphisms318.ofTop_top_one _)
end ClutchedModuleTop318
