module
public import PullbackSquareTarget318
public section
noncomputable section
namespace CoverComparisonRectangle318
open AlgebraicGeometry CategoryTheory ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {S₁ S₂ T₁ T₂ U₁ U₂ B₁ B₂ : Scheme.{u}}
  (f₁ : S₁ ⟶ T₁) (f₂ : S₂ ⟶ T₂) (g₁ : U₁ ⟶ B₁) (g₂ : U₂ ⟶ B₂)
  (p₁ : U₁ ⟶ S₁) (q₁ : B₁ ⟶ T₁) (h₁ : p₁ ≫ f₁ = g₁ ≫ q₁)
  (p₂ : U₂ ⟶ S₂) (q₂ : B₂ ⟶ T₂) (h₂ : p₂ ≫ f₂ = g₂ ≫ q₂)
  (a : S₂ ⟶ S₁) (b : T₂ ⟶ T₁) (hs : a ≫ f₁ = f₂ ≫ b)
  (a' : U₂ ⟶ U₁) (b' : B₂ ⟶ B₁) (ho : a' ≫ g₁ = g₂ ≫ b')
  (ha : a' ≫ p₁ = p₂ ≫ a) (hb : b' ≫ q₁ = q₂ ≫ b)

/-- The actual four square comparisons commute around a rectangle.
This is derived from the two original canonical pasting equations, rather
than requiring a new coherence law for the chosen charts. -/
lemma rectangle (M : T₁.Modules) :
    (Scheme.Modules.pullback a').map ((coverComparison f₁ g₁ p₁ q₁ h₁).hom.app M) ≫
      (coverComparison g₁ g₂ a' b' ho).hom.app ((Scheme.Modules.pullback q₁).obj M) ≫
        (Scheme.Modules.pullback g₂).map ((coverComparison q₁ q₂ b' b hb).hom.app M) =
    (coverComparison p₁ p₂ a' a ha).hom.app ((Scheme.Modules.pullback f₁).obj M) ≫
      (Scheme.Modules.pullback p₂).map ((coverComparison f₁ f₂ a b hs).hom.app M) ≫
        (coverComparison f₂ g₂ p₂ q₂ h₂).hom.app ((Scheme.Modules.pullback b).obj M) := by
  have hc : (a' ≫ p₁) ≫ f₁ = g₂ ≫ (b' ≫ q₁) :=
    CanonicalBaseChangePasting318.square_composition f₁ g₁ g₂ p₁ q₁ h₁ a' b' ho
  have hl := SheafComparisonPasting318.cover_pasting f₁ g₁ g₂ p₁ q₁ h₁ a' b' ho
    (a' ≫ p₁) (b' ≫ q₁) hc rfl rfl M
  have hr := SheafComparisonPasting318.cover_pasting f₁ f₂ g₂ a b hs p₂ q₂ h₂
    (a' ≫ p₁) (b' ≫ q₁) hc ha.symm hb.symm M
  apply (cancel_mono ((Scheme.Modules.pullback g₂).map
    ((PullbackPathComposition318.iso q₂ b (b' ≫ q₁) hb.symm).hom.app M))).mp
  rw [PullbackSquareTarget318.cover_common q₁ q₂ b' b hb (b' ≫ q₁) rfl hb.symm,
    PullbackSquareTarget318.cover_common p₁ p₂ a' a ha (a' ≫ p₁) rfl ha.symm]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc,
    PullbackSquareTarget318.map_inv_hom_assoc, PullbackSquareTarget318.map_inv_hom, Iso.inv_hom_id_app, Category.comp_id]
  rw [← hl, ← hr]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
end CoverComparisonRectangle318
