module
public import LocalCoordinateRelation318
public import ClutchedCoordinateFrames318
public section
noncomputable section
namespace ClutchedCoordinateRelations318
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
    (s₀ t₀ : Γ(Y₀,⊤)) (s₁ t₁ : Γ(Y₁,⊤))
    (hs : k₀.appTop s₀=k₁.appTop s₁*a) (ht : k₀.appTop t₀=k₁.appTop t₁*a)

@[expose] def first_relation (ha : IsUnit a) (hr : j₁⁻¹ᵁ j₀.opensRange=k₁.opensRange)
    (b : Γ(Y₀,⊤)) (hb : t₀=b*s₀) :=
  LocalCoordinateRelation318.relation j₀ (firstFrame j₀ j₁ k₀ k₁ h a ha hr)
    (ClutchedModuleTop318.map j₀ j₁ k₀ k₁ h a s₀ s₁ hs)
    (ClutchedModuleTop318.map j₀ j₁ k₀ k₁ h a t₀ t₁ ht) b s₀ t₀
    (ClutchedCoordinateFrames318.first_value j₀ j₁ k₀ k₁ h a s₀ s₁ hs ha hr)
    (ClutchedCoordinateFrames318.first_value j₀ j₁ k₀ k₁ h a t₀ t₁ ht ha hr) hb

@[expose] def second_relation (hr : j₀⁻¹ᵁ j₁.opensRange=k₀.opensRange)
    (b : Γ(Y₁,⊤)) (hb : t₁=b*s₁) :=
  LocalCoordinateRelation318.relation j₁ (secondFrame j₀ j₁ k₀ k₁ h a hr)
    (ClutchedModuleTop318.map j₀ j₁ k₀ k₁ h a s₀ s₁ hs)
    (ClutchedModuleTop318.map j₀ j₁ k₀ k₁ h a t₀ t₁ ht) b s₁ t₁
    (ClutchedCoordinateFrames318.second_value j₀ j₁ k₀ k₁ h a s₀ s₁ hs hr)
    (ClutchedCoordinateFrames318.second_value j₀ j₁ k₀ k₁ h a t₀ t₁ ht hr) hb
end ClutchedCoordinateRelations318
