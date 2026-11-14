module
public import SelectedCurveUnits318
public section
noncomputable section
namespace SelectedProductDepth318
open ContactPatternSupport318 ClearedContactForms318 MergedContactPrimePattern318 ConcretePadic318
set_option maxHeartbeats 1000000

/-- A positive prime row has depth exactly one at its own selected prime
and zero at the other four distinct positions. -/
theorem factor_values (k : Fin 5 → ℤ) (hk : ∀ i, 0<k i)
    (hp : ∀ i, (k i).natAbs.Prime) (hi : Function.Injective k) (i : Fin 5) :
    let p := (k i).natAbs
    letI : Fact p.Prime := ⟨hp i⟩
    ∀ j : Fin 5, rationalPlace p (k j:ℚ)=if j=i then 1 else 0 := by
  dsimp only
  let p := (k i).natAbs
  letI : Fact p.Prime := ⟨hp i⟩
  have hcast (j : Fin 5) : (k j:ℚ)=((k j).natAbs:ℚ) := by
    exact_mod_cast (show k j=((k j).natAbs:ℤ) by
      rw [Int.natCast_natAbs,abs_of_pos (hk j)])
  intro j
  rw [hcast j]
  by_cases hj : j=i
  · subst j
    rw [if_pos rfl,rational_value p _ (by exact_mod_cast (hp i).ne_zero),
      padicValRat.self (hp i).one_lt]
  · rw [if_neg hj]
    apply rational_nat_unit p _
    intro hd
    have he : (k i).natAbs=(k j).natAbs :=
      (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp hd
    have hc : k i=k j := by
      have hc := congrArg (fun n : ℕ => (n:ℤ)) he
      simpa only [Int.natCast_natAbs,abs_of_pos (hk i),abs_of_pos (hk j)] using hc
    exact hj (hi hc).symm

/-- Exact valuation of the actual five-factor integer product, not an
assumption that one arbitrary contact factor has simple valuation. -/
theorem product_value (k : Fin 5 → ℤ) (hk : ∀ i, 0<k i)
    (hp : ∀ i, (k i).natAbs.Prime) (hi : Function.Injective k) (i : Fin 5) :
    let p := (k i).natAbs
    letI : Fact p.Prime := ⟨hp i⟩
    rationalPlace p (DetectorPrimeProduct318.product k:ℚ)=1 := by
  dsimp only
  let p := (k i).natAbs
  letI : Fact p.Prime := ⟨hp i⟩
  have hv := factor_values k hk hp hi i
  rw [DetectorPrimeProduct318.product_cast]
  simp only [(rationalPlace p).map_mul,hv]
  fin_cases i <;> norm_num

/-- Every literal row of the three-detector family has simple selected
prime depth; duplicate factors across different rows cause no problem. -/
theorem actual_product {labels : Fin 4 → ℤ} (C : Clearing labels)
    (hn : ∀ j, labels j≠0) (u w : ℤ) (hp : Values C u w) (j : Fin 3) (i : Fin 5) :
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    rationalPlace p (DetectorPrimeProduct318.product (row C u w j):ℚ)=1 :=
  product_value (row C u w j) (row_pos C u w hp j) (row_prime C u w hp j)
    (row_distinct C hn u w hp j) i

end SelectedProductDepth318
