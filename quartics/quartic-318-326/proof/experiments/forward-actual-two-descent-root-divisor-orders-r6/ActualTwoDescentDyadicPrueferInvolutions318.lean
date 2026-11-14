module
public import ActualTwoDescentDyadicPrueferModel318
public section
noncomputable section
namespace ActualTwoDescentDyadicPrueferInvolutions318
set_option maxHeartbeats 16000000

open ActualTwoDescentDyadicPrueferModel318 ActualTwoDescentPrimaryPowerLevels318

abbrev CircleTwo := {x : AddCircle (1 : ℚ) // (2 : ℕ) • x=0}

lemma actual_circle_two_finite : Finite CircleTwo :=
  (AddCircle.finite_torsion (1 : ℚ) (by decide : 0<(2 : ℕ))).to_subtype

lemma actual_circle_two_card : Nat.card CircleTwo ≤ 2 := by
  letI := actual_circle_two_finite
  have hreg : IsSMulRegular ℚ (2 : ℕ) := by
    intro x y h
    have h' : (2 : ℚ)*x=2*y := by simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h
    linarith
  have h := AddCircle.card_torsion_le_of_isSMulRegular (1 : ℚ) 2 (by decide) hreg
  change ENat.card CircleTwo ≤ (2 : ℕ) at h
  rw [ENat.card_eq_coe_natCard] at h
  exact_mod_cast h

def prueferTwoInclusion : powerLevel PrueferTwo 1 → CircleTwo := fun x =>
  ⟨x.val.val.toAdd,by
    have h := congrArg (fun z : PrueferTwo => z.val.toAdd) x.property
    change (2^1) • x.val.val.toAdd=0 at h
    simpa only [pow_one] using h⟩

lemma actual_pruefer_two_inclusion_injective : Function.Injective prueferTwoInclusion := by
  intro x y h
  apply Subtype.ext; apply Subtype.ext
  exact congrArg Multiplicative.ofAdd (congrArg Subtype.val h)

lemma actual_pruefer_two_finite : Finite (powerLevel PrueferTwo 1) := by
  letI := actual_circle_two_finite
  exact Finite.of_injective prueferTwoInclusion actual_pruefer_two_inclusion_injective

lemma actual_pruefer_two_card : Nat.card (powerLevel PrueferTwo 1) ≤ 2 := by
  letI := actual_circle_two_finite
  exact (Nat.card_le_card_of_injective prueferTwoInclusion actual_pruefer_two_inclusion_injective).trans actual_circle_two_card

end ActualTwoDescentDyadicPrueferInvolutions318
