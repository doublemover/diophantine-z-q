module
public import ConcreteFourPrimeOrders318
public import ExactContinuityDivisibilityCRT318
public section
noncomputable section
namespace ConcreteFourPrimeCompatibility318
open ConcreteFourPrimeOrders318
/-- Literal LCMs of the four native quotient orders just produced. -/
def primaryLCM : ℕ := Finset.univ.lcm primary
def oppositeLCM : ℕ := Finset.univ.lcm opposite
lemma primary_bound : primaryLCM∣2076550380760355089 := by
  apply Finset.lcm_dvd
  intro i hi
  rw [primary_eq]
  fin_cases i <;> norm_num [primeOrder]
lemma opposite_bound : oppositeLCM∣494696448982544 := by
  apply Finset.lcm_dvd
  intro i hi
  apply (opposite_dvd i).trans
  fin_cases i <;> norm_num [oddFactor]
/-- Cross-index compatibility is proved for this concrete independent family.
It is not inferred from separate same-prime coprimality. -/
theorem cross_coprime : Nat.Coprime primaryLCM oppositeLCM :=
  (Nat.Coprime.of_dvd_left primary_bound
    (by decide : Nat.Coprime 2076550380760355089 494696448982544)).of_dvd_right opposite_bound
lemma primary_continuity : Nat.Coprime primaryLCM 16 :=
  Nat.Coprime.of_dvd_left primary_bound (by decide : Nat.Coprime 2076550380760355089 16)
lemma prime_product_primary : Nat.Coprime 525101129559015828641 primaryLCM :=
  Nat.Coprime.of_dvd_right primary_bound
    (by decide : Nat.Coprime 525101129559015828641 2076550380760355089)
lemma prime_product_opposite : Nat.Coprime 525101129559015828641 oppositeLCM :=
  Nat.Coprime.of_dvd_right opposite_bound
    (by decide : Nat.Coprime 525101129559015828641 494696448982544)
/-- The fixed product is exactly the product of these four primes, not the old Pi. -/
lemma product_eq : Finset.univ.prod primeValue=525101129559015828641 := by
  norm_num [primeValue,Fin.prod_univ_succ]
/-- A genuine nondegenerate original row has FIVE distinct prime values.
It cannot be supplied by these FOUR primes, even allowing repeated assignments. -/
theorem not_original_row_assignment {labels : Fin 4 → ℤ}
    (C : ClearedContactForms318.Clearing labels) (hn : ∀ j, labels j≠0)
    (u w : ℤ) (hv : MergedContactPrimePattern318.Values C u w) (j : Fin 3) :
    ¬∃ f : Fin 5 → Fin 4, ∀ k,
      ClearedContactForms318.value u w (C.coefficient (j,k))=(primeValue (f k):ℤ) := by
  rintro ⟨f,hf⟩
  have hi : Function.Injective f := by
    intro k l h
    apply MergedContactPrimePattern318.row_distinct C hn u w hv j
    rw [hf k,hf l,h]
  have hc := Fintype.card_le_of_injective f hi
  norm_num at hc
end ConcreteFourPrimeCompatibility318
