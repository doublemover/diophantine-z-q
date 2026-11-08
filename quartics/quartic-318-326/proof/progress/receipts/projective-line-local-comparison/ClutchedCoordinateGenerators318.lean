module
public import ClutchedCoordinateFrames318
public import NormalizedSectionFrame318
public section
noncomputable section
namespace ClutchedCoordinateGenerators318
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

/-- A unit first coefficient makes the actual coordinate sheaf map a local isomorphism. -/
theorem first_isIso (ha : IsUnit a) (hr : j₁⁻¹ᵁ j₀.opensRange=k₁.opensRange)
    (hs₀ : IsUnit s₀) :
    IsIso ((Scheme.Modules.restrictFunctor j₀).map (ClutchedModuleTop318.map
      j₀ j₁ k₀ k₁ h a s₀ s₁ hs)) :=
  NormalizedSectionFrame318.restrict_isIso j₀ _ (firstFrame j₀ j₁ k₀ k₁ h a ha hr)
    _ s₀ hs₀ (ClutchedCoordinateFrames318.first_value j₀ j₁ k₀ k₁ h a s₀ s₁ hs ha hr)

/-- A unit second coefficient makes the actual coordinate sheaf map a local isomorphism. -/
theorem second_isIso (hr : j₀⁻¹ᵁ j₁.opensRange=k₀.opensRange) (hs₁ : IsUnit s₁) :
    IsIso ((Scheme.Modules.restrictFunctor j₁).map (ClutchedModuleTop318.map
      j₀ j₁ k₀ k₁ h a s₀ s₁ hs)) :=
  NormalizedSectionFrame318.restrict_isIso j₁ _ (secondFrame j₀ j₁ k₀ k₁ h a hr)
    _ s₁ hs₁ (ClutchedCoordinateFrames318.second_value j₀ j₁ k₀ k₁ h a s₀ s₁ hs hr)
end ClutchedCoordinateGenerators318
