module
public import AffineOpenChartNaturality318
public section
noncomputable section
namespace CanonicalCoverPastingInverse318
open AlgebraicGeometry CategoryTheory
open ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

lemma inverse_pasting {C : Type u} [Category.{v} C] {A B C₁ D E : C}
    (α : A ≅ B) (β : B ≅ C₁) (γ : A ≅ D) (δ : D ≅ E) (ε : E ≅ C₁)
    (h : α.hom ≫ β.hom = γ.hom ≫ δ.hom ≫ ε.hom) :
    δ.inv ≫ γ.inv ≫ α.hom = ε.hom ≫ β.inv := by
  apply (cancel_mono β.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.id_comp]

variable {B₀ B₁ B₂ U₀ U₁ U₂ : Scheme.{u}}
  (f₀ : U₀ ⟶ B₀) (f₁ : U₁ ⟶ B₁) (f₂ : U₂ ⟶ B₂)
  (a₁ : U₁ ⟶ U₀) (b₁ : B₁ ⟶ B₀) (h₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
  (a₂ : U₂ ⟶ U₁) (b₂ : B₂ ⟶ B₁) (h₂ : a₂ ≫ f₁ = f₂ ≫ b₂)
  (a₃ : U₂ ⟶ U₀) (b₃ : B₂ ⟶ B₀) (h₃ : a₃ ≫ f₀ = f₂ ≫ b₃)
  (ha : a₂ ≫ a₁ = a₃) (hb : b₂ ≫ b₁ = b₃)

/-- The inverse original cover comparisons paste through the named
source and base composition maps. This is a consequence of the proved
canonical cover-pasting law, not another coherence input. -/
lemma cover_pasting (M : B₀.Modules) :
    (coverComparison f₁ f₂ a₂ b₂ h₂).inv.app ((Scheme.Modules.pullback b₁).obj M) ≫
      (Scheme.Modules.pullback a₂).map ((coverComparison f₀ f₁ a₁ b₁ h₁).inv.app M) ≫
        (PullbackPathComposition318.iso a₂ a₁ a₃ ha).hom.app
          ((Scheme.Modules.pullback f₀).obj M) =
    (Scheme.Modules.pullback f₂).map ((PullbackPathComposition318.iso b₂ b₁ b₃ hb).hom.app M) ≫
      (coverComparison f₀ f₂ a₃ b₃ h₃).inv.app M := by
  subst a₃
  subst b₃
  exact inverse_pasting
    ((PullbackPathComposition318.iso a₂ a₁ (a₂ ≫ a₁) rfl).app ((Scheme.Modules.pullback f₀).obj M))
    ((coverComparison f₀ f₂ (a₂ ≫ a₁) (b₂ ≫ b₁)
      (CanonicalBaseChangePasting318.square_composition f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂)).app M)
    ((Scheme.Modules.pullback a₂).mapIso ((coverComparison f₀ f₁ a₁ b₁ h₁).app M))
    ((coverComparison f₁ f₂ a₂ b₂ h₂).app ((Scheme.Modules.pullback b₁).obj M))
    ((Scheme.Modules.pullback f₂).mapIso ((PullbackPathComposition318.iso b₂ b₁ (b₂ ≫ b₁) rfl).app M))
    (CanonicalBaseChangePasting318.cover_pasting f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ M)
end CanonicalCoverPastingInverse318
