module
public import OriginalBaseLineOpenUnit318
public section
noncomputable section
namespace CanonicalLocalMapCompatibility318
open AlgebraicGeometry CategoryTheory ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 3000000
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
  (M N : Y.Modules) (e : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
  (u₁ : (Scheme.Modules.pullback b₁).obj M ⟶ (Scheme.Modules.pullback b₁).obj N)
  (u₂ : (Scheme.Modules.pullback b₂).obj M ⟶ (Scheme.Modules.pullback b₂).obj N)

/-- Two chart maps recovering the same original covering map satisfy the
original nested base-path square after pullback. This follows entirely
from original canonical pasting and naturality, before faithfulness. -/
lemma after_cover
    (hU : (coverComparison f f₁ a₁ b₁ h₁).hom.app M ≫ (Scheme.Modules.pullback f₁).map u₁ =
      (Scheme.Modules.pullback a₁).map e ≫ (coverComparison f f₁ a₁ b₁ h₁).hom.app N)
    (hV : (coverComparison f f₂ a₂ b₂ h₂).hom.app M ≫ (Scheme.Modules.pullback f₂).map u₂ =
      (Scheme.Modules.pullback a₂).map e ≫ (coverComparison f f₂ a₂ b₂ h₂).hom.app N) :
    (Scheme.Modules.pullback f₂).map
      ((Scheme.Modules.pullback b).map u₁ ≫ (PullbackPathComposition318.iso b b₁ b₂ hb).hom.app N) =
    (Scheme.Modules.pullback f₂).map
      ((PullbackPathComposition318.iso b b₁ b₂ hb).hom.app M ≫ u₂) := by
  let c := coverComparison f₁ f₂ a b h
  have hn := c.hom.naturality u₁
  have hp := (PullbackPathComposition318.iso a a₁ a₂ ha).hom.naturality e
  simp only [Functor.comp_map] at hn hp
  have hU' := congrArg ((Scheme.Modules.pullback a).map) hU
  simp only [Functor.map_comp] at hU'
  have hM := SheafComparisonPasting318.cover_pasting f f₁ f₂ a₁ b₁ h₁ a b h a₂ b₂ h₂ ha hb M
  have hN := SheafComparisonPasting318.cover_pasting f f₁ f₂ a₁ b₁ h₁ a b h a₂ b₂ h₂ ha hb N
  apply (cancel_epi ((Scheme.Modules.pullback a).map ((coverComparison f f₁ a₁ b₁ h₁).hom.app M) ≫
    c.hom.app ((Scheme.Modules.pullback b₁).obj M))).mp
  simp only [Functor.map_comp,Category.assoc]
  rw [← Category.assoc (c.hom.app ((Scheme.Modules.pullback b₁).obj M)),← hn]
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback a).map ((coverComparison f f₁ a₁ b₁ h₁).hom.app M)),hU']
  simp only [Category.assoc]
  rw [← hN,← Category.assoc ((Scheme.Modules.pullback a).map ((Scheme.Modules.pullback a₁).map e)),hp]
  simp only [Category.assoc]
  rw [← hV,← Category.assoc ((PullbackPathComposition318.iso a a₁ a₂ ha).hom.app
    ((Scheme.Modules.pullback f).obj M)),hM]
  simp only [Category.assoc]
end CanonicalLocalMapCompatibility318
