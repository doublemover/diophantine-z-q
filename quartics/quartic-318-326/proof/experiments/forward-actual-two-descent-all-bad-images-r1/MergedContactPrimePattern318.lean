module
public import ActualContactPrimeSquareclasses318
public section
noncomputable section
namespace MergedContactPrimePattern318
open ContactPrimeForms318 ClearedContactForms318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- The finite prime-value output of the precise analytic prime theorem.
This structure does NOT assert that such an output exists. Gaussian rays,
reduction orders and rational point realization remain separate inputs. -/
structure Values (u w : ℤ) : Prop where
  nonzero : w≠0
  positive : ∀ k∈coefficients C, 0<value u w k
  prime : ∀ k∈coefficients C, Nat.Prime (value u w k).natAbs

@[expose] def product (u w : ℤ) : ℕ :=
  ∏ k∈coefficients C, (value u w k).natAbs

lemma product_pos (u w : ℤ) (h : Values C u w) : 0<product C u w := by
  apply Finset.prod_pos
  intro k hk
  exact (h.prime k hk).pos

lemma selected_divides (u w : ℤ) (i : Fin 3 × Fin 5) :
    (value u w (C.coefficient i)).natAbs∣product C u w :=
  Finset.dvd_prod_of_mem _ (coefficient_mem C i)

lemma all_positions_prime (u w : ℤ) (h : Values C u w) (i : Fin 3 × Fin 5) :
    0<value u w (C.coefficient i) ∧ Nat.Prime (value u w (C.coefficient i)).natAbs :=
  ⟨h.positive _ (coefficient_mem C i),h.prime _ (coefficient_mem C i)⟩

lemma value_injective (u w : ℤ) (hw : w≠0) : Function.Injective (value u w) := by
  intro k l he
  have hm : k*w^2=l*w^2 := add_left_cancel he
  exact (mul_right_inj' (pow_ne_zero 2 hw)).mp hm

lemma row_distinct (hn : ∀ j, labels j≠0) (u w : ℤ) (h : Values C u w) (j : Fin 3) :
    Function.Injective (fun k => value u w (C.coefficient (j,k))) :=
  (value_injective u w h.nonzero).comp (row_injective C hn j)

/-- Each actual row is attached to a product of its five distinct positive
prime values, while a single merged product covers all fifteen positions. -/
theorem actual_squareclasses (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ)
    (hp : Values C u w)
    (hb : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness q labels h
      (parameter C u w) (190+51*j.val)) :
    0<product C u w ∧
    ∀ j : Fin 3,
      Function.Injective (fun k => value u w (C.coefficient (j,k))) ∧
      (∀ k : Fin 5, Nat.Prime (value u w (C.coefficient (j,k))).natAbs ∧
        (value u w (C.coefficient (j,k))).natAbs∣product C u w) ∧
      ∃ z : ℚ, z≠0 ∧
        ThreeDetectorUniformFamily318.witness q labels h (parameter C u w) (190+51*j.val)=
          (rowProduct C u w j:ℚ)*z^2 := by
  refine ⟨product_pos C u w hp,?_⟩
  intro j
  refine ⟨row_distinct C hn u w hp j,?_,
    ActualContactPrimeSquareclasses318.squareFactor C q h u w j,
    ActualContactPrimeSquareclasses318.squareFactor_ne C hn q h u w hp.nonzero j (hb j),
    ActualContactPrimeSquareclasses318.witness C hn q h u w hp.nonzero j⟩
  intro k
  exact ⟨(all_positions_prime C u w hp (j,k)).2,selected_divides C u w (j,k)⟩

end MergedContactPrimePattern318
