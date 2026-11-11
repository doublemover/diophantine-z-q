module
public import AffineOriginalCoverComparison318
public section
noncomputable section
namespace OriginalCoverComparisonPasting318
open AlgebraicGeometry CategoryTheory ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U₁ B₁ U₂ B₂ : Scheme.{u}}
  (f : X ⟶ Y) (f₁ : U₁ ⟶ B₁) (f₂ : U₂ ⟶ B₂)
  (a₁ : U₁ ⟶ X) (b₁ : B₁ ⟶ Y) (h₁ : a₁ ≫ f = f₁ ≫ b₁)
  (a : U₂ ⟶ U₁) (b : B₂ ⟶ B₁) (h : a ≫ f₁ = f₂ ≫ b)
  (a₂ : U₂ ⟶ X) (b₂ : B₂ ⟶ Y) (h₂ : a₂ ≫ f = f₂ ≫ b₂)
  (ha : a ≫ a₁ = a₂) (hb : b ≫ b₁ = b₂)
  (K : Y.Modules) (L : X.Modules) (M₁ : B₁.Modules) (M₂ : B₂.Modules)
  (u₁ : (Scheme.Modules.pullback b₁).obj K ⟶ M₁)
  (u₂ : (Scheme.Modules.pullback b₂).obj K ⟶ M₂)
  (t : (Scheme.Modules.pullback b).obj M₁ ⟶ M₂)
  (e₁ : (Scheme.Modules.pullback f₁).obj M₁ ⟶ (Scheme.Modules.pullback a₁).obj L)
  (e₂ : (Scheme.Modules.pullback f₂).obj M₂ ⟶ (Scheme.Modules.pullback a₂).obj L)

/-- Original chart reconstruction squares and a proved base-chart
comparison equation give compatibility of the actual covering-line maps.
Both source and base pullback paths are retained explicitly. -/
lemma comparison_pasting
    (hu : (Scheme.Modules.pullback b).map u₁ ≫ t =
      (PullbackPathComposition318.iso b b₁ b₂ hb).hom.app K ≫ u₂)
    (he : (Scheme.Modules.pullback f₂).map t ≫ e₂ =
      (coverComparison f₁ f₂ a b h).inv.app M₁ ≫
        (Scheme.Modules.pullback a).map e₁ ≫
          (PullbackPathComposition318.iso a a₁ a₂ ha).hom.app L) :
    (Scheme.Modules.pullback a).map
        ((coverComparison f f₁ a₁ b₁ h₁).hom.app K ≫
          (Scheme.Modules.pullback f₁).map u₁ ≫ e₁) ≫
      (PullbackPathComposition318.iso a a₁ a₂ ha).hom.app L =
    (PullbackPathComposition318.iso a a₁ a₂ ha).hom.app ((Scheme.Modules.pullback f).obj K) ≫
      (coverComparison f f₂ a₂ b₂ h₂).hom.app K ≫
        (Scheme.Modules.pullback f₂).map u₂ ≫ e₂ := by
  have he' : (Scheme.Modules.pullback a).map e₁ ≫
      (PullbackPathComposition318.iso a a₁ a₂ ha).hom.app L =
    (coverComparison f₁ f₂ a b h).hom.app M₁ ≫
      (Scheme.Modules.pullback f₂).map t ≫ e₂ := by
    rw [he]
    simp only [Category.assoc,Iso.hom_inv_id_app_assoc]
  have hn := (coverComparison f₁ f₂ a b h).hom.naturality u₁
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp,Category.assoc]
  rw [he']
  rw [← Category.assoc ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f₁).map u₁)),
    hn,Category.assoc,← Functor.map_comp_assoc,hu,Functor.map_comp]
  have hp := SheafComparisonPasting318.cover_pasting f f₁ f₂ a₁ b₁ h₁ a b h a₂ b₂ h₂ ha hb K
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (Scheme.Modules.pullback f₂).map u₂ ≫ e₂) hp.symm
end OriginalCoverComparisonPasting318
