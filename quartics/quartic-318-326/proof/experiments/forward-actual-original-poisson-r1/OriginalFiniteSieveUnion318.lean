module
public import OriginalReciprocalSquareTail318
public section
noncomputable section
namespace OriginalFiniteSieveUnion318
open scoped BigOperators
set_option maxHeartbeats 3000000

/-- Overlap-safe finite union count. A point is assigned one actual
witness index, never counted as if the prime obstruction sets were disjoint. -/
theorem finite_union_card {X I : Type*} [Fintype X] [Fintype I]
    (P : I → X → Prop) :
    Nat.card {x : X // ∃ i, P i x}≤∑ i, Nat.card {x : X // P i x} := by
  classical
  let f : {x : X // ∃ i, P i x} → Σ i, {x : X // P i x} := fun x =>
    ⟨Classical.choose x.2,x.1,Classical.choose_spec x.2⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun a : Σ i, {x : X // P i x} => a.2.1) he)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using hh

/-- General actual finite obstruction family with produced1/p² bounds.
The reciprocal-square estimate is proved by finite telescoping, not
assumed from prime distribution or an unproved sieve input. -/
theorem finite_small_prime_tail {X : Type*} [Fintype X] (S : Finset ℕ)
    (P : ↥S → X → Prop) (Y : ℕ) (hY : 0<Y) (hcut : ∀ p∈S, Y<p)
    (C : ℝ) (hC : 0≤C)
    (hbound : ∀ p : ↥S, (Nat.card {x : X // P p x}:ℝ)≤C/(p.1:ℝ)^2) :
    (Nat.card {x : X // ∃ p : ↥S, P p x}:ℝ)≤C/(Y:ℝ) := by
  classical
  have hc : (Nat.card {x : X // ∃ p : ↥S, P p x}:ℝ)≤
      ∑ p : ↥S, (Nat.card {x : X // P p x}:ℝ) := by
    exact_mod_cast finite_union_card P
  have hs := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hbound p)
  have he : (∑ p : ↥S, C/(p.1:ℝ)^2)=C*(∑ p∈S,1/(p:ℝ)^2) := by
    rw [←Finset.sum_coe_sort S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have htail := OriginalReciprocalSquareTail318.finite_reciprocal_tail Y hY S hcut
  calc
    _ ≤ ∑ p : ↥S, C/(p.1:ℝ)^2 := hc.trans hs
    _ = C*(∑ p∈S,1/(p:ℝ)^2) := he
    _ ≤ C*(1/(Y:ℝ)) := mul_le_mul_of_nonneg_left htail hC
    _ = C/(Y:ℝ) := by ring

end OriginalFiniteSieveUnion318
