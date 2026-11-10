module
public import OriginalFiniteDeckGalois318
public import OriginalArithmeticBranchReconstruction318
public section
noncomputable section
namespace OriginalDeckArithmeticLabels318
abbrev ArithmeticGroup := Multiplicative InertiaLabels318.V
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  (ρ : ArithmeticGroup →* (L ≃ₐ[RatFunc ℚ] L)) (hfaithful : Function.Injective ρ)
  (hfixed : ∀ x : L, (∀ w : ArithmeticGroup, ρ w x = x) →
    ∃ r : RatFunc ℚ, algebraMap (RatFunc ℚ) L r = x)

/-- The OLD original field's arithmetic labels are the inverse of its SAME
actual finite deck representation, proved exhaustive by the fixed field. -/
@[expose] def labels : (L ≃ₐ[RatFunc ℚ] L) ≃* ArithmeticGroup :=
  (OriginalFiniteDeckGalois318.equivalence ρ hfaithful hfixed).symm

lemma labels_apply (w : ArithmeticGroup) : labels ρ hfaithful hfixed (ρ w) = w := by
  rw [← OriginalFiniteDeckGalois318.equivalence_apply ρ hfaithful hfixed w]
  exact (OriginalFiniteDeckGalois318.equivalence ρ hfaithful hfixed).symm_apply_apply w

lemma reconstruct (σ : L ≃ₐ[RatFunc ℚ] L) :
    ρ (labels ρ hfaithful hfixed σ) = σ := by
  rw [← OriginalFiniteDeckGalois318.equivalence_apply ρ hfaithful hfixed
    (labels ρ hfaithful hfixed σ)]
  exact (OriginalFiniteDeckGalois318.equivalence ρ hfaithful hfixed).apply_symm_apply σ

include ρ hfaithful hfixed in
/-- The actual degree16 is a consequence of that original deck action.
It is not an assumption used to select a replacement field. -/
theorem degree_sixteen : Module.finrank (RatFunc ℚ) L = 16 := by
  rw [OriginalFiniteDeckGalois318.finrank ρ hfaithful hfixed]
  change Nat.card (Fin 4 → ZMod 2) = 16
  norm_num [Nat.card_eq_fintype_card]
end OriginalDeckArithmeticLabels318
