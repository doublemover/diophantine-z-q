module
public import AffineOpenChartComposition318
public section
noncomputable section
namespace SheafComparisonPasting318
open AlgebraicGeometry CategoryTheory ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B₀ B₁ B₂ U₀ U₁ U₂ : Scheme.{u}}
  (f₀ : U₀ ⟶ B₀) (f₁ : U₁ ⟶ B₁) (f₂ : U₂ ⟶ B₂)
  (a₁ : U₁ ⟶ U₀) (b₁ : B₁ ⟶ B₀) (h₁ : a₁ ≫ f₀ = f₁ ≫ b₁)
  (a₂ : U₂ ⟶ U₁) (b₂ : B₂ ⟶ B₁) (h₂ : a₂ ≫ f₁ = f₂ ≫ b₂)
  (a₃ : U₂ ⟶ U₀) (b₃ : B₂ ⟶ B₀) (h₃ : a₃ ≫ f₀ = f₂ ≫ b₃)
  (ha : a₂ ≫ a₁ = a₃) (hb : b₂ ≫ b₁ = b₃)

lemma cover_pasting (M : B₀.Modules) :
    (PullbackPathComposition318.iso a₂ a₁ a₃ ha).hom.app ((Scheme.Modules.pullback f₀).obj M) ≫
      (coverComparison f₀ f₂ a₃ b₃ h₃).hom.app M =
    (Scheme.Modules.pullback a₂).map ((coverComparison f₀ f₁ a₁ b₁ h₁).hom.app M) ≫
      (coverComparison f₁ f₂ a₂ b₂ h₂).hom.app ((Scheme.Modules.pullback b₁).obj M) ≫
        (Scheme.Modules.pullback f₂).map ((PullbackPathComposition318.iso b₂ b₁ b₃ hb).hom.app M) := by
  subst a₃
  subst b₃
  exact CanonicalBaseChangePasting318.cover_pasting f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ M

variable {M₀ : B₀.Modules} {M₁ : B₁.Modules} {M₂ : B₂.Modules}
  (t₁ : (Scheme.Modules.pullback b₁).obj M₀ ⟶ M₁)
  (t₂ : (Scheme.Modules.pullback b₂).obj M₁ ⟶ M₂)
  (t₃ : (Scheme.Modules.pullback b₃).obj M₀ ⟶ M₂)

/-- Actual commuting-square pullback comparisons preserve a proved
transition composition equation, with both original path normalizations. -/
lemma transition_pasting
    (ht : (Scheme.Modules.pullback b₂).map t₁ ≫ t₂ =
      (PullbackPathComposition318.iso b₂ b₁ b₃ hb).hom.app M₀ ≫ t₃) :
    (Scheme.Modules.pullback a₂).map
        ((coverComparison f₀ f₁ a₁ b₁ h₁).hom.app M₀ ≫ (Scheme.Modules.pullback f₁).map t₁) ≫
      (coverComparison f₁ f₂ a₂ b₂ h₂).hom.app M₁ ≫ (Scheme.Modules.pullback f₂).map t₂ =
    (PullbackPathComposition318.iso a₂ a₁ a₃ ha).hom.app ((Scheme.Modules.pullback f₀).obj M₀) ≫
      (coverComparison f₀ f₂ a₃ b₃ h₃).hom.app M₀ ≫ (Scheme.Modules.pullback f₂).map t₃ := by
  have hn := (coverComparison f₁ f₂ a₂ b₂ h₂).hom.naturality t₁
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback a₂).map ((Scheme.Modules.pullback f₁).map t₁)),
    hn, Category.assoc, ← Functor.map_comp, ht, Functor.map_comp]
  have hp := cover_pasting f₀ f₁ f₂ a₁ b₁ h₁ a₂ b₂ h₂ a₃ b₃ h₃ ha hb M₀
  simpa only [Category.assoc] using congrArg (fun q => q ≫ (Scheme.Modules.pullback f₂).map t₃) hp.symm
end SheafComparisonPasting318
