module
public import SelectedThreeBranchSignedDegree318
public import SelectedSameWitnessGlobalBudget318
public section
noncomputable section
open NumberField SelectedJOneExactMinorLoss318
open SelectedThreeBranchSignedDegree318 SelectedSameWitnessGlobalBudget318
open scoped BigOperators

namespace SelectedSameMapDegreeFinite318

section SameCover
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
variable (M : ℕ) [NeZero M]
local notation "d" => Module.finrank K F

/-- Applied with K=L(j), F=L(X₁(M)), and g the rank of the actual
ordered Hodge minor. Degree is finite field degree, not the level of
the chosen primitive form. The geometric inputs are only the actual
generic sign-class comparison and the actual degree of div(dj). -/
theorem degree_genus_cap {g c0 c1728 cinf : ℕ}
    (large : 3 < M) (rank : V M ↪ ℕ)
    (degree : d = (representatives (primitive M) rank).card)
    (atZero : 3*c0 = d) (at1728 : 2*c1728 = d) (cusp : 0 < cinf)
    (canonical : 2*(g:ℤ)-2 = 2*(c0:ℤ)+c1728-d-cinf) :
    2*d ≤ M^2 ∧ 12*g+6*cinf=d+12 ∧ 2*g-2<d ∧
      (g:ℝ) ≤ (M:ℝ)^2/24+1/2 := by
  have hd : 0 < d := Module.finrank_pos
  have half : 2*d ≤ M^2 := by
    rw [degree]
    exact primitive_twice_bound M (by omega) rank
  obtain ⟨eq,cap,strict⟩ := bounded_genus hd atZero at1728 cusp canonical
  have hG : 12*(g:ℝ) ≤ (d:ℝ)+6 := by exact_mod_cast cap
  have hD : 2*(d:ℝ) ≤ (M:ℝ)^2 := by exact_mod_cast half
  refine ⟨half,eq,strict,?_⟩
  linarith only [hG,hD]

end SameCover

section Finite
variable {L : Type*} [Field L] [NumberField L] {g : ℕ}
variable (m : Matrix (Fin g) (Fin g) L)
variable (C : FinitePlace L → Matrix (Fin g) (Fin g) L)
variable (I : (v : FinitePlace L) → Matrix (Fin g) (Fin g) (integralAt v))
variable (M : ℕ) (V T W : Finset (FinitePlace L))
local notation "D" => (Module.finrank ℚ L:ℝ)
local notation "q" => fun v => (m.det*(C v).det)⁻¹
local notation "loss" => fun v => (baseMatrix v (I v)).det

/-- Multiply the already proved same-witness finite inequality by the
new bound for the rank of THIS very matrix. The exact normalized loss
is not dropped or redefined. In particular no independent height of a
reference surface is accepted here. -/
theorem off_level_finite_cap (hM : 0 < M)
    (genus : (g:ℝ) ≤ (M:ℝ)^2/24+1/2)
    (sameBudget : degree q + degree loss ≤
      (g:ℝ)*((∑ v ∈ V, finiteLog v (M:L)) +
        (∑ v ∈ W, finiteLog v (1727:L)) + (∑ v ∈ T, finiteLog v (157:L))/2) / D)
    (fallbackAway : ∀ v ∈ W, v (157:L) = 1) :
    degree q + degree loss ≤
      ((M:ℝ)^2/24+1/2)*(Real.log (M:ℝ)+Real.log 11+Real.log 157/2) := by
  have hm : 1 ≤ (M:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hM
  have hcost : 0 ≤ Real.log (M:ℝ)+Real.log 11+Real.log 157/2 :=
    add_nonneg (add_nonneg (Real.log_nonneg hm) (Real.log_nonneg (by norm_num)))
      (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num))
  exact (sameBudget.trans (off_level_157_bound g M hM V T W fallbackAway)).trans
    (mul_le_mul_of_nonneg_right genus hcost)

/-- Full collision fallback with the same degree-scaled rank. It
requires the actual no-tame finite witness; it does not manufacture
any local -1727M integral witness from the genus bound. -/
theorem full_finite_cap (hM : 0 < M)
    (genus : (g:ℝ) ≤ (M:ℝ)^2/24+1/2)
    (sameBudget : degree q + degree loss ≤
      (g:ℝ)*((∑ v ∈ V, finiteLog v (M:L)) +
        (∑ v ∈ W, finiteLog v (1727:L))) / D) :
    degree q + degree loss ≤ ((M:ℝ)^2/24+1/2)*(Real.log (M:ℝ)+Real.log 1727) := by
  have hm : 1 ≤ (M:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hM
  have hcost : 0 ≤ Real.log (M:ℝ)+Real.log 1727 :=
    add_nonneg (Real.log_nonneg hm) (Real.log_nonneg (by norm_num))
  exact (sameBudget.trans (no_tame_bound g M hM V W)).trans
    (mul_le_mul_of_nonneg_right genus hcost)

end Finite
end SelectedSameMapDegreeFinite318

#print axioms SelectedSameMapDegreeFinite318.degree_genus_cap
#print axioms SelectedSameMapDegreeFinite318.off_level_finite_cap
#print axioms SelectedSameMapDegreeFinite318.full_finite_cap
