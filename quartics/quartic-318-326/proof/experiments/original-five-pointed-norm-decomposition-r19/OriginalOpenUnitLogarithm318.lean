module
public import OriginalThickenedOpenSections318
public section
noncomputable section
namespace OriginalOpenUnitLogarithm318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpen318 OriginalThickenedOpenSections318
universe u
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R)
    (V : X.Opens) [IsAffine V.toScheme]
local notation "E" => (sectionsIso R p V).commRingCatIsoToRingEquiv
local notation "B" => (baseIso V).commRingCatIsoToRingEquiv
/-- The actual local logarithm transported through the original open-immersion
section maps. Its coefficient is an original section on V, not a new coordinate. -/
@[expose] def exp (a : Γ(X,V)) : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ :=
  Units.map E.symm.toMonoidHom (OriginalAffineUnitLogarithm318.exp R (localBase R p V) (B a))
@[expose] def log (z : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ) : Γ(X,V) :=
  B.symm (OriginalAffineUnitLogarithm318.log R (localBase R p V) (Units.map E.toMonoidHom z))
lemma exp_original (a : Γ(X,V)) : exp R p V a =
    InfinitesimalUnitCocycle318.unit (thickening R p)
      (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p)
      (π R p ⁻¹ᵁ V) ((π R p).app V a) := by
  apply Units.ext
  apply E.injective
  change E (E.symm (OriginalAffineUnitLogarithm318.exp R (localBase R p V) (B a) :
    Γ(Local R p V,⊤))) = E (1 + _ * _)
  rw [E.apply_symm_apply, OriginalAffineUnitLogarithm318.exp_original]
  change 1 + DualNumberInfinitesimalLines318.epsilon R (localBase R p V) *
    (π R (localBase R p V)).appTop (B a) = E (1 + _ * _)
  rw [map_add, map_one, map_mul]
  rw [show E (InfinitesimalUnitCocycle318.epsilon (thickening R p)
    (DualNumberInfinitesimalLines318.epsilon R p) (π R p ⁻¹ᵁ V)) =
    DualNumberInfinitesimalLines318.epsilon R (localBase R p V) from epsilon_square R p V]
  exact congrArg (fun x => 1 + DualNumberInfinitesimalLines318.epsilon R (localBase R p V) * x)
    (congrArg (fun f => f a) (coefficient_square R p V)).symm
lemma log_exp (a : Γ(X,V)) : log R p V (exp R p V a) = a := by
  have h : Units.map E.toMonoidHom (exp R p V a) =
      OriginalAffineUnitLogarithm318.exp R (localBase R p V) (B a) := by
    apply Units.ext
    exact E.apply_symm_apply _
  dsimp only [log]
  rw [h, OriginalAffineUnitLogarithm318.log_exp, B.symm_apply_apply]
lemma exp_injective : Function.Injective (exp R p V) := fun a b h => by
  simpa only [log_exp] using congrArg (log R p V) h
lemma exp_log (z : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ)
    (hz : reduce R p V z.val = 1) : exp R p V (log R p V z) = z := by
  have hred : (reduction R (localBase R p V)).appTop (E z.val) = 1 := by
    have h := congrArg (fun f => f z.val) (reduction_square R p V)
    change (reduction R (localBase R p V)).appTop (E z.val) = B (reduce R p V z.val) at h
    simpa only [hz, map_one] using h
  have h := OriginalAffineUnitLogarithm318.exp_log R (localBase R p V)
    (Units.map E.toMonoidHom z) hred
  apply Units.ext
  apply E.injective
  change E (E.symm (OriginalAffineUnitLogarithm318.exp R (localBase R p V)
    (B (B.symm (OriginalAffineUnitLogarithm318.log R (localBase R p V)
      (Units.map E.toMonoidHom z)))) : Γ(Local R p V,⊤))) = E z.val
  rw [B.apply_symm_apply, E.apply_symm_apply]
  exact congrArg Units.val h
lemma reduction_exp (a : Γ(X,V)) : reduce R p V (exp R p V a).val = 1 := by
  apply B.injective
  have h := congrArg (fun f => f (exp R p V a).val) (reduction_square R p V)
  change (reduction R (localBase R p V)).appTop (E (E.symm
    (OriginalAffineUnitLogarithm318.exp R (localBase R p V) (B a) : Γ(Local R p V,⊤)))) =
      B (reduce R p V (exp R p V a).val) at h
  rw [E.apply_symm_apply, OriginalAffineUnitLogarithm318.reduction_exp] at h
  simpa only [map_one] using h.symm
lemma unit_iff (z : Γ(thickening R p,π R p ⁻¹ᵁ V)ˣ) :
    reduce R p V z.val = 1 ↔ ∃! a : Γ(X,V), exp R p V a = z := by
  constructor
  · intro hz
    exact ⟨log R p V z, exp_log R p V z hz, fun a ha =>
      exp_injective R p V (ha.trans (exp_log R p V z hz).symm)⟩
  · rintro ⟨a,rfl,_⟩
    exact reduction_exp R p V a
lemma exp_add (a b : Γ(X,V)) : exp R p V (a + b) = exp R p V a * exp R p V b := by
  dsimp only [exp]
  rw [map_add, OriginalAffineUnitLogarithm318.exp_add, map_mul]
end OriginalOpenUnitLogarithm318
