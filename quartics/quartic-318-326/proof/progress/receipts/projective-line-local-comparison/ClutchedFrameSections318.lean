module
public import ClutchedModuleFrames318
public import OpenPushforwardGlobalValue318
public section
noncomputable section
namespace ClutchedFrameSections318
open AlgebraicGeometry CategoryTheory Opposite
open ClutchedModule318 ClutchedModuleFrames318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y₀ Y₁ W : Scheme.{u}}
    (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion k₀] [IsOpenImmersion k₁]
    (h : k₁≫j₁=k₀≫j₀) (a : Γ(W,⊤))

theorem firstFrame_top (ha : IsUnit a)
    (hr : j₁⁻¹ᵁ j₀.opensRange=k₁.opensRange) (s : Γ(sheaf j₀ j₁ k₀ k₁ h a,⊤)) :
    (firstFrame j₀ j₁ k₀ k₁ h a ha hr).hom.app ⊤
      ((sheaf j₀ j₁ k₀ k₁ h a).presheaf.map
        (homOfLE (show j₀ ''ᵁ ⊤≤⊤ from le_top)).op s)=
      (first j₀ j₁ k₀ k₁ h a).app ⊤ s :=
  OpenPushforwardGlobalValue318.localMap_top j₀ _ (unit Y₀) (first j₀ j₁ k₀ k₁ h a) s

theorem secondFrame_top
    (hr : j₀⁻¹ᵁ j₁.opensRange=k₀.opensRange) (s : Γ(sheaf j₀ j₁ k₀ k₁ h a,⊤)) :
    (secondFrame j₀ j₁ k₀ k₁ h a hr).hom.app ⊤
      ((sheaf j₀ j₁ k₀ k₁ h a).presheaf.map
        (homOfLE (show j₁ ''ᵁ ⊤≤⊤ from le_top)).op s)=
      (second j₀ j₁ k₀ k₁ h a).app ⊤ s :=
  OpenPushforwardGlobalValue318.localMap_top j₁ _ (unit Y₁) (second j₀ j₁ k₀ k₁ h a) s
end ClutchedFrameSections318
