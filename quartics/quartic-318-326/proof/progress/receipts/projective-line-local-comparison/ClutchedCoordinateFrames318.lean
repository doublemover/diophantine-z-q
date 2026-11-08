module
public import ClutchedFrameSections318
public import ClutchedModuleTop318
public section
noncomputable section
namespace ClutchedCoordinateFrames318
open AlgebraicGeometry CategoryTheory
open ClutchedModule318 ClutchedModuleFrames318 ClutchedModuleTop318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y₀ Y₁ W : Scheme.{u}}
    (j₀ : Y₀ ⟶ X) (j₁ : Y₁ ⟶ X) (k₀ : W ⟶ Y₀) (k₁ : W ⟶ Y₁)
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion k₀] [IsOpenImmersion k₁]
    (h : k₁≫j₁=k₀≫j₀) (a : Γ(W,⊤))
    (s₀ : Γ(Y₀,⊤)) (s₁ : Γ(Y₁,⊤)) (hs : k₀.appTop s₀=k₁.appTop s₁*a)

/-- The genuine first frame has exactly the specified local coefficient. -/
theorem first_value (ha : IsUnit a) (hr : j₁⁻¹ᵁ j₀.opensRange=k₁.opensRange) :
    (firstFrame j₀ j₁ k₀ k₁ h a ha hr).hom.app ⊤
      ((sheaf j₀ j₁ k₀ k₁ h a).presheaf.map
        (homOfLE (show j₀ ''ᵁ ⊤≤⊤ from le_top)).op
          (sectionTop j₀ j₁ k₀ k₁ h a s₀ s₁ hs))=s₀ :=
  (ClutchedFrameSections318.firstFrame_top j₀ j₁ k₀ k₁ h a ha hr _).trans
    (ClutchedModuleTop318.first_value j₀ j₁ k₀ k₁ h a s₀ s₁ hs)

/-- The genuine second frame has exactly the specified local coefficient. -/
theorem second_value (hr : j₀⁻¹ᵁ j₁.opensRange=k₀.opensRange) :
    (secondFrame j₀ j₁ k₀ k₁ h a hr).hom.app ⊤
      ((sheaf j₀ j₁ k₀ k₁ h a).presheaf.map
        (homOfLE (show j₁ ''ᵁ ⊤≤⊤ from le_top)).op
          (sectionTop j₀ j₁ k₀ k₁ h a s₀ s₁ hs))=s₁ :=
  (ClutchedFrameSections318.secondFrame_top j₀ j₁ k₀ k₁ h a hr _).trans
    (ClutchedModuleTop318.second_value j₀ j₁ k₀ k₁ h a s₀ s₁ hs)
end ClutchedCoordinateFrames318
