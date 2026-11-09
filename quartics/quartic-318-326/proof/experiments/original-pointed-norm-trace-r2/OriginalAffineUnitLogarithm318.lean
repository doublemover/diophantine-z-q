module
public import OriginalAffineDualSectionEquivalence318
public section
noncomputable section
namespace OriginalAffineUnitLogarithm318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} [IsAffine X] (p : X ⟶ base R)
local notation "E" => OriginalAffineDualSectionEquivalence318.equivalence R p
/-- Actual infinitesimal units in the original thickening section ring. -/
@[expose] def exp (a : Γ(X,⊤)) : Γ(thickening R p,⊤)ˣ :=
  Units.map E.toMonoidHom (SquareZeroUnit318.unit Γ(X,⊤) a)
/-- Logarithms are the second coordinate of the ACTUAL original section map. -/
@[expose] def log (z : Γ(thickening R p,⊤)ˣ) : Γ(X,⊤) := (E.symm (z : Γ(thickening R p,⊤))).snd
lemma exp_original (a : Γ(X,⊤)) : exp R p a =
    InfinitesimalUnitCocycle318.infinitesimal (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p)
      ((pullback.fst p (structureMap R)).appTop a) := by
  apply Units.ext
  change OriginalDualSectionLift318.lift R p (1 + TrivSqZeroExt.inr a) = _
  simp [OriginalDualSectionLift318.lift, SquareZeroRingLift318.lift,
    InfinitesimalUnitCocycle318.infinitesimal]
lemma reduction_exp (a : Γ(X,⊤)) : (reduction R p).appTop (exp R p a : Γ(thickening R p,⊤)) = 1 := by
  change (reduction R p).appTop (OriginalDualSectionLift318.lift R p (1 + TrivSqZeroExt.inr a)) = 1
  rw [OriginalDualSectionLift318.reduction_lift]
  simp
lemma log_exp (a : Γ(X,⊤)) : log R p (exp R p a) = a := by
  change (E.symm (E (SquareZeroUnit318.unit Γ(X,⊤) a : SquareZeroUnit318.Dual Γ(X,⊤)))).snd = a
  rw [RingEquiv.symm_apply_apply]
  simp [SquareZeroUnit318.unit]
lemma exp_injective : Function.Injective (exp R p) := fun a b h => by
  have hh := congrArg (log R p) h
  simpa only [log_exp] using hh
/-- Every original unit reducing to1 is the actual1+epsilon times a UNIQUE
original coefficient. This is stronger than nonzero-field representative data. -/
lemma exp_log (z : Γ(thickening R p,⊤)ˣ)
    (hz : (reduction R p).appTop (z : Γ(thickening R p,⊤)) = 1) : exp R p (log R p z) = z := by
  let w : (SquareZeroUnit318.Dual Γ(X,⊤))ˣ := Units.map E.symm.toMonoidHom z
  have hw : (w : SquareZeroUnit318.Dual Γ(X,⊤)).fst = 1 :=
    (OriginalAffineDualSectionEquivalence318.inverse_fst R p _).trans hz
  have h := congrArg (fun u : (SquareZeroUnit318.Dual Γ(X,⊤))ˣ => E (u : SquareZeroUnit318.Dual Γ(X,⊤)))
    (SquareZeroUnit318.unit_eq_of_fst Γ(X,⊤) w hw)
  apply Units.ext
  simpa [exp, log, w] using h
lemma unit_iff (z : Γ(thickening R p,⊤)ˣ) :
    (reduction R p).appTop (z : Γ(thickening R p,⊤)) = 1 ↔ ∃! a : Γ(X,⊤), exp R p a = z := by
  constructor
  · intro hz
    exact ⟨log R p z, exp_log R p z hz, fun a ha =>
      exp_injective R p (ha.trans (exp_log R p z hz).symm)⟩
  · rintro ⟨a,rfl,_⟩
    exact reduction_exp R p a
lemma exp_add (a b : Γ(X,⊤)) : exp R p (a + b) = exp R p a * exp R p b := by
  change Units.map E.toMonoidHom (SquareZeroUnit318.unit Γ(X,⊤) (a + b)) = _
  rw [SquareZeroUnit318.unit_add, map_mul]
lemma exp_neg (a : Γ(X,⊤)) : exp R p (-a) = (exp R p a)⁻¹ := by
  change Units.map E.toMonoidHom (SquareZeroUnit318.unit Γ(X,⊤) (-a)) = _
  rw [SquareZeroUnit318.unit_neg, map_inv]
lemma log_mul (z w : Γ(thickening R p,⊤)ˣ)
    (hz : (reduction R p).appTop (z : Γ(thickening R p,⊤)) = 1)
    (hw : (reduction R p).appTop (w : Γ(thickening R p,⊤)) = 1) :
    log R p (z * w) = log R p z + log R p w := by
  calc
    log R p (z * w) = log R p (exp R p (log R p z + log R p w)) := by
      rw [exp_add, exp_log R p z hz, exp_log R p w hw]
    _ = _ := log_exp R p _
end OriginalAffineUnitLogarithm318
