module
public import ActualPreparedFourRankConsumer318
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public section
noncomputable section

namespace ActualCommonIndexedAuxiliaryPrime318

open ActualPreparedPoleSquarefreeClasses318

/-- One actual auxiliary prime for a whole finite set of positive integral twist
parameters. It is not one of the primes constructing the twists, and it does
not by itself provide an odd Selmer bound. -/
theorem common_auxiliary_prime (S : Finset ℕ) (hS : ∀ t ∈ S, 0 < t) :
    ∃ p : ℕ, p.Prime ∧ Nat.ModEq 28 p 5 ∧ ∀ t ∈ S, ¬ p ∣ t := by
  have hcop : Nat.Coprime 5 28 := by decide
  have hmod : (28 : ℕ) ≠ 0 := by decide
  obtain ⟨p, hlt, hp, hres⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (S.sup id) hmod hcop
  refine ⟨p, hp, hres, ?_⟩
  intro t ht hdvd
  have htmax : t ≤ S.sup id := Finset.le_sup (f := id) ht
  exact (not_lt_of_ge (Nat.le_of_dvd (hS t ht) hdvd)) (lt_of_le_of_lt htmax hlt)

/-- With the already chosen classes at THESE poles and their same n_i, avoid
all eight entries simultaneously. Duplicates, e.g. theta_i=1, are harmless. -/
theorem four_pairs_common_prime (b : Fin 4 → ℚ) (C : ∀ i, Classes (b i))
    (n : Fin 4 → ℕ) (hn : ∀ i, 0 < n i) :
    ∃ p : ℕ, p.Prime ∧ Nat.ModEq 28 p 5 ∧
      (∀ i, ¬ p ∣ n i) ∧ (∀ i, ¬ p ∣ n i * (C i).theta) := by
  classical
  let S : Finset ℕ := Finset.univ.image n ∪
    Finset.univ.image (fun i => n i * (C i).theta)
  have hS : ∀ t ∈ S, 0 < t := by
    intro t ht
    change t ∈ Finset.univ.image n ∪
      Finset.univ.image (fun i => n i * (C i).theta) at ht
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact hn i
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact Nat.mul_pos (hn i) (C i).theta_pos
  obtain ⟨p, hp, hm, havoids⟩ := common_auxiliary_prime S hS
  refine ⟨p, hp, hm, ?_, ?_⟩
  · intro i
    apply havoids
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro i
    apply havoids
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

end ActualCommonIndexedAuxiliaryPrime318
