module
public import ActualTZChoiceJointDensity318
public import ActualTZLiteralAbsoluteEuler318
import all ActualTZLiteralAbsoluteEuler318
import all ActualTZChoiceJointDensity318
import all ActualTZRegulatedPhysicalBounds318
public section
noncomputable section
namespace ActualTZSignedPrimeSlotWeight318
open scoped BigOperators ArithmeticFunction.Moebius
open ActualTZRegulatedLocalFactor318 ActualTZRegulatedPhysicalBounds318
open ActualTZBooleanPrimeSlots318 ActualTZPrimeUniverseDigits318
open ActualTZChoiceJointDensity318 ActualTZMultiLinearCRT318

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] def exponent (s u : I→ℂ) (j : Slot I) : ℂ :=
  if j.2 then s j.1 else u j.1

private theorem slot_pick_product (P : ℕ) (x : Choices I P) (j : Slot I) (z : ℂ) :
    (∏ p : PrimeAt P,pick ((p.val:ℂ)^(-z)) (bit P x p j)) =
      ((μ (digit P x j):ℤ):ℂ)*(digit P x j:ℂ)^(-z) := by
  classical
  let T := (mask P x j).val
  have ht (p : ℕ) (hp : p∈T) : p.Prime :=
    Nat.prime_of_mem_primesBelow ((mask P x j).property hp)
  have hd : digit P x j = ∏ p∈T,p := digit_prod P x j
  calc
    _ = ∏ p : PrimeAt P,if p.val∈T then -((p.val:ℂ)^(-z)) else 1 := by
      apply Finset.prod_congr rfl
      intro p _
      by_cases h : bit P x p j=true
      · simp only [pick,h,if_true,if_pos ((mem_mask P x p j).2 h)]
      · simp only [pick,if_neg h,if_neg (fun h' => h ((mem_mask P x p j).1 h'))]
    _ = ∏ p∈Nat.primesBelow P,if p∈T then -((p:ℂ)^(-z)) else 1 :=
      Finset.prod_coe_sort _ _
    _ = ∏ p∈T,-((p:ℂ)^(-z)) := by
      rw [←Finset.prod_filter,Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (mask P x j).property]
    _ = _ := by
      rw [hd,signed_mobius T ht,Int.cast_prod,
        cpow_product T (fun p hp => (ht p hp).pos),←Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun p _ => by simp)

/-- This is the actual signed Möbius weight, not the absolute-majorant
version. The pairing of old slots and all prime powers is unchanged. -/
theorem signed_amplitude (P : ℕ) (x : Choices I P) (s u : I→ℂ) :
    (∏ p : PrimeAt P,amplitude (regulator p.val s) (regulator p.val u) (x p).1 (x p).2) =
      (∏ j : Slot I,((μ (digit P x j):ℤ):ℂ))*
      ∏ j : Slot I,(digit P x j:ℂ)^(-exponent s u j) := by
  classical
  calc
    _ = ∏ p : PrimeAt P,∏ j : Slot I,
        pick ((p.val:ℂ)^(-exponent s u j)) (bit P x p j) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [amplitude,Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.prod_bool]
      simp only [amplitude,regulator,exponent,bit,if_true,if_false]
    _ = ∏ j : Slot I,∏ p : PrimeAt P,
        pick ((p.val:ℂ)^(-exponent s u j)) (bit P x p j) := Finset.prod_comm
    _ = ∏ j : Slot I,((μ (digit P x j):ℤ):ℂ)*(digit P x j:ℂ)^(-exponent s u j) := by
      apply Finset.prod_congr rfl
      intro j _
      exact slot_pick_product P x j (exponent s u j)
    _ = _ := Finset.prod_mul_distrib

/-- Pointwise exact on the same prime assignment and original wrap
cell. Multiplication by an arbitrary shared frequency factor (in
particular ∏ φ) may follow this identity. -/
theorem signed_choice (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (s u : I→ℂ) (x : Choices I P) :
    ActualTZLiteralAbsoluteEuler318.choiceWeight W P a b s u x =
    (jointDensity W (digit P x) (a ∘ Prod.fst) (b ∘ Prod.fst):ℂ)*
      (∏ j : Slot I,((μ (digit P x j):ℤ):ℂ))*
      ∏ j : Slot I,(digit P x j:ℂ)^(-exponent s u j) := by
  change (∏ p : PrimeAt P,
    amplitude (regulator p.val s) (regulator p.val u) (x p).1 (x p).2 *
      localChoice W P a b x p)=_
  rw [Finset.prod_mul_distrib,signed_amplitude,←density_from_choices W P a b hU x] <;> ac_rfl

end ActualTZSignedPrimeSlotWeight318
