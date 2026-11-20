module
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic
public section
noncomputable section
open NumberField
open scoped BigOperators

namespace SelectedFiniteIntegerBudget318
variable {L : Type*} [Field L] [NumberField L]

/-- Full normalized mass of a rational integer controls every finite
subset of actual places of L, even when 157 is split or ramified. -/
theorem natural_budget (n : ℕ) (hn : 0 < n) (V : Finset (FinitePlace L)) :
    (∑ v ∈ V, -Real.log (v (n:L))) ≤ (Module.finrank ℚ L:ℝ)*Real.log (n:ℝ) := by
  classical
  have hn0 : (n:L) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hS := FinitePlace.hasFiniteMulSupport hn0
  let S := hS.toFinset
  have hv (v : FinitePlace L) : 0 < v (n:L) := FinitePlace.pos_iff.mpr hn0
  have hv1 (v : FinitePlace L) : v (n:L) ≤ 1 := by
    rw [← FinitePlace.norm_embedding_eq]
    simpa only [map_natCast] using FinitePlace.norm_le_one L v.maximalIdeal (n:𝓞 L)
  have hnorm : (∏ v ∈ S, v (n:L)) = ((n:ℝ)^Module.finrank ℚ L)⁻¹ := by
    change (∏ v ∈ hS.toFinset, v (n:L)) = _
    rw [←finprod_eq_prod _ hS,FinitePlace.prod_eq_inv_abs_norm hn0,Algebra.norm_natCast,
      abs_of_nonneg (show 0 ≤ (n:ℚ)^Module.finrank ℚ L by positivity)]
    push_cast
  have hlogs := congrArg Real.log hnorm
  rw [Real.log_prod (fun v _ => (hv v).ne'),Real.log_inv,Real.log_pow] at hlogs
  have htotal : (∑ v ∈ S, -Real.log (v (n:L))) = (Module.finrank ℚ L:ℝ)*Real.log (n:ℝ) := by
    rw [Finset.sum_neg_distrib,hlogs,neg_neg]
  have hoff (v : FinitePlace L) (h : v ∉ S) : v (n:L) = 1 := by
    by_contra hn'
    exact h (hS.mem_toFinset.mpr hn')
  calc
    _ = ∑ v ∈ V ∩ S, -Real.log (v (n:L)) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro v hv hnot
      have hvS : v ∉ S := fun hh => hnot (Finset.mem_inter.mpr ⟨hv,hh⟩)
      rw [hoff v hvS,Real.log_one,neg_zero]
    _ ≤ ∑ v ∈ S, -Real.log (v (n:L)) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun v _ _ => neg_nonneg.mpr (Real.log_nonpos (hv v).le (hv1 v)))
    _ = _ := htotal

/-- For the off-level 157 lane, the same-minor finite rows are at most
half contact per differential. Weight by the evaluation field once. -/
theorem aggregate_157 (g : ℕ) (V : Finset (FinitePlace L))
    (row : FinitePlace L → ℝ)
    (hrow : ∀ v ∈ V, row v ≤ ((g:ℝ)/2)*(-Real.log (v (157:L)))) :
    (∑ v ∈ V, row v) / (Module.finrank ℚ L:ℝ) ≤ ((g:ℝ)/2)*Real.log 157 := by
  have hdim : 0 < (Module.finrank ℚ L:ℝ) := by
    exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=L))
  apply (div_le_iff₀ hdim).mpr
  calc
    _ ≤ ∑ v ∈ V, ((g:ℝ)/2)*(-Real.log (v (157:L))) := Finset.sum_le_sum hrow
    _ = ((g:ℝ)/2)*(∑ v ∈ V, -Real.log (v (157:L))) := by rw [Finset.mul_sum]
    _ ≤ ((g:ℝ)/2)*((Module.finrank ℚ L:ℝ)*Real.log 157) :=
      mul_le_mul_of_nonneg_left (natural_budget (L:=L) 157 (by decide) V) (by positivity)
    _ = _ := by ring

end SelectedFiniteIntegerBudget318

#print axioms SelectedFiniteIntegerBudget318.natural_budget
#print axioms SelectedFiniteIntegerBudget318.aggregate_157
