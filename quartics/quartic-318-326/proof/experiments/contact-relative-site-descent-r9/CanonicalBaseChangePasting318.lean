module
public import AffineBaseChangeNaturality318
public section
noncomputable section
namespace CanonicalBaseChangePasting318
open AlgebraicGeometry CategoryTheory
open ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B₀ B₁ B₂ U₀ U₁ U₂ : Scheme.{u}}
  (f₀ : U₀ ⟶ B₀) (f₁ : U₁ ⟶ B₁) (f₂ : U₂ ⟶ B₂)
  (a₁ : U₁ ⟶ U₀) (b₁ : B₁ ⟶ B₀) (h₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
  (a₂ : U₂ ⟶ U₁) (b₂ : B₂ ⟶ B₁) (h₂ : a₂ ≫ f₁ = f₂ ≫ b₂)

lemma square_composition : (a₂ ≫ a₁) ≫ f₀ = f₂ ≫ (b₂ ≫ b₁) := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]

/-- Pasting original commuting squares gives precisely the composition of
the original covering-object comparisons, including both actual pullback
associators. This is derived from three named-path associativity equations. -/
lemma cover_pasting (M : B₀.Modules) :
    (PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).hom.app
        ((Scheme.Modules.pullback f₀).obj M) ≫
      (coverComparison f₀ f₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
        (square_composition f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂)).hom.app M =
    (Scheme.Modules.pullback a₂).map ((coverComparison f₀ f₁ a₁ b₁ h₁).hom.app M) ≫
      (coverComparison f₁ f₂ a₂ b₂ h₂).hom.app ((Scheme.Modules.pullback b₁).obj M) ≫
        (Scheme.Modules.pullback f₂).map
          ((PullbackPathComposition318.iso b₂ b₁ (b₂ ≫ b₁) rfl).hom.app M) := by
  have ht : a₂ ≫ (f₁ ≫ b₁) = f₂ ≫ (b₂ ≫ b₁) := by
    rw [← Category.assoc, h₂, Category.assoc]
  have hp : (f₂ ≫ b₂) ≫ b₁ = f₂ ≫ (b₂ ≫ b₁) := Category.assoc _ _ _
  have hl := PullbackPathComposition318.assoc a₂ a₁ f₀ (a₂ ≫ a₁) (f₁ ≫ b₁)
    (f₂ ≫ (b₂ ≫ b₁)) rfl h₁
    (square_composition f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂) ht M
  have hm := PullbackPathComposition318.assoc a₂ f₁ b₁ (f₂ ≫ b₂) (f₁ ≫ b₁)
    (f₂ ≫ (b₂ ≫ b₁)) h₂ rfl hp ht M
  have hr := PullbackPathComposition318.assoc f₂ b₂ b₁ (f₂ ≫ b₂) (b₂ ≫ b₁)
    (f₂ ≫ (b₂ ≫ b₁)) rfl rfl hp rfl M
  apply (cancel_mono ((PullbackPathComposition318.iso f₂ (b₂ ≫ b₁)
    (f₂ ≫ (b₂ ≫ b₁)) rfl).hom.app M)).mp
  simp only [coverComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [hl, ← hr, Iso.inv_hom_id_app_assoc, hm]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
end CanonicalBaseChangePasting318
