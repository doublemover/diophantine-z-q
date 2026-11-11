module
public import OriginalThickenedPointedFrame318
public section
noncomputable section
namespace PointedFrameTransitionReduction318
open AlgebraicGeometry CategoryTheory
open PointedLineDeformation318
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) (L : Deformation i)
    (e₀ e₁ : PointedIso i L (trivial i))
/-- The actual unit-sheaf automorphism comparing two pointed frames. -/
@[expose] def transition : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  e₀.iso.symm ≪≫ e₁.iso
@[expose] def scalar : Γ(X,⊤)ˣ := UnitSheafScalar318.unit (transition i L e₀ e₁)
/-- Exact special-fiber compatibility forces the ORIGINAL transition unit to
reduce to1. No statement about its value in a function field is used. -/
lemma scalar_reduces : i.appTop (scalar i L e₀ e₁ : Γ(X,⊤)) = 1 := by
  let t := (trivial i).trivialization
  have hh : (Scheme.Modules.pullback i).map (transition i L e₀ e₁).hom ≫ t.hom = t.hom := by
    change (Scheme.Modules.pullback i).map (e₀.iso.inv ≫ e₁.iso.hom) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, e₁.compatible, ← e₀.compatible,
      ← Functor.map_comp_assoc, e₀.iso.inv_hom_id, Functor.map_id, Category.id_comp]
  rw [UnitSheafScalar318.hom_multiply, ← ModuleScalar318.unit_eq,
    ModuleScalarPullback318.pullback_map, ModuleScalar318.natural,
    ModuleScalar318.unit_eq] at hh
  have hm : ClutchedModule318.multiply (i.appTop (scalar i L e₀ e₁ : Γ(X,⊤))) = 𝟙 _ := by
    apply (cancel_epi t.hom).1
    simpa only [Category.comp_id] using hh
  have hv := congrArg (fun k => k.app ⊤ (1 : Γ(X₀,⊤))) hm
  simpa only [ClutchedModule318.multiply_top, mul_one] using hv
lemma unit_trans (e f : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    UnitSheafScalar318.unit (e ≪≫ f) = UnitSheafScalar318.unit e * UnitSheafScalar318.unit f := by
  apply UnitSheafScalar318.unique
  change e.hom ≫ f.hom = ClutchedModule318.multiply _
  rw [UnitSheafScalar318.hom_multiply, UnitSheafScalar318.hom_multiply,
    ← ModuleScalar318.unit_eq, ← ModuleScalar318.unit_eq,
    ModuleScalarPullback318.map_mul, ModuleScalar318.unit_eq]
lemma scalar_comp (e₂ : PointedIso i L (trivial i)) :
    scalar i L e₀ e₁ * scalar i L e₁ e₂ = scalar i L e₀ e₂ := by
  change UnitSheafScalar318.unit (e₀.iso.symm ≪≫ e₁.iso) *
    UnitSheafScalar318.unit (e₁.iso.symm ≪≫ e₂.iso) = _
  rw [← unit_trans]
  congr 1
  apply Iso.ext
  simp
variable (R : Type u) [CommRing R] {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ DualNumberScheme318.base R)
    (M : DualNumberScheme318.Deformation R p)
    (f₀ f₁ : PointedIso (DualNumberScheme318.reduction R p) M
      (trivial (DualNumberScheme318.reduction R p)))
/-- Every original affine pointed-frame discrepancy has a UNIQUE coefficient,
with the exact scalar and the previously constructed canonical exponential. -/
lemma unique_log : ∃! a : Γ(Y,⊤), OriginalAffineUnitLogarithm318.exp R p a =
    scalar (DualNumberScheme318.reduction R p) M f₀ f₁ :=
  (OriginalAffineUnitLogarithm318.unit_iff R p _).1
    (scalar_reduces (DualNumberScheme318.reduction R p) M f₀ f₁)
/-- The actual multiplicative pointed-frame cocycle gives its full additive
logarithm law, before any quotient or cohomological classification. -/
lemma logarithm_cocycle
    (f₂ : PointedIso (DualNumberScheme318.reduction R p) M
      (trivial (DualNumberScheme318.reduction R p))) :
    OriginalAffineUnitLogarithm318.log R p (scalar (DualNumberScheme318.reduction R p) M f₀ f₁) +
      OriginalAffineUnitLogarithm318.log R p (scalar (DualNumberScheme318.reduction R p) M f₁ f₂) =
    OriginalAffineUnitLogarithm318.log R p (scalar (DualNumberScheme318.reduction R p) M f₀ f₂) := by
  rw [← OriginalAffineUnitLogarithm318.log_mul R p _ _
    (scalar_reduces _ _ _ _) (scalar_reduces _ _ _ _), scalar_comp]
end PointedFrameTransitionReduction318
