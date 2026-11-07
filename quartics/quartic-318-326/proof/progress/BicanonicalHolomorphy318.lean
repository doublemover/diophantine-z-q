module
public import BicanonicalCharts318
public section
noncomputable section
namespace BicanonicalHolomorphy318
open BicanonicalCharts318 LiteralMetricExtension318 Set
open scoped Topology
set_option maxHeartbeats 0

theorem polynomial_holomorphic (a : Fin 4 → ℂ) : Differentiable ℂ (contactPolynomial a) := by
  intro z
  unfold contactPolynomial
  fun_prop

theorem branch_den_holomorphic (a : Fin 4 → ℂ) (i : Fin 4) : Differentiable ℂ (branchDen a i) := by
  intro z
  unfold branchDen
  fun_prop

theorem infinity_den_holomorphic (a : Fin 4 → ℂ) : Differentiable ℂ (infinityDen a) := by
  intro z
  unfold infinityDen
  fun_prop

theorem polynomial_nonzero_iff (a : Fin 4 → ℂ) (t : ℂ) :
    contactPolynomial a t ≠ 0 ↔ ∀ j, t ≠ a j := by
  simp [contactPolynomial, Finset.prod_ne_zero_iff, sub_ne_zero]

theorem source_holomorphic (a : Fin 4 → ℂ) :
    DifferentiableOn ℂ (q0 a) {t | contactPolynomial a t ≠ 0} ∧
    DifferentiableOn ℂ (q1 a) {t | contactPolynomial a t ≠ 0} := by
  constructor
  · intro z hz
    exact ((differentiableAt_const (1 : ℂ)).div (polynomial_holomorphic a z) hz).differentiableWithinAt
  · intro z hz
    exact (differentiableAt_id.mul
      ((differentiableAt_const (1 : ℂ)).div (polynomial_holomorphic a z) hz)).differentiableWithinAt

theorem source_no_common_zero (a : Fin 4 → ℂ) (z : ℂ) (hz : contactPolynomial a z ≠ 0) :
    q0 a z ≠ 0 := one_div_ne_zero hz

theorem branch_den_nonzero (a : Fin 4 → ℂ) (ha : Function.Injective a) (i : Fin 4) :
    branchDen a i 0 ≠ 0 := by
  unfold branchDen
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  simpa using sub_ne_zero.mpr (ha.ne (Ne.symm j.property))

theorem branch_holomorphic (a : Fin 4 → ℂ) (i : Fin 4) :
    DifferentiableOn ℂ (branchQ0 a i) {z | branchDen a i z ≠ 0} ∧
    DifferentiableOn ℂ (branchQ1 a i) {z | branchDen a i z ≠ 0} := by
  constructor
  · intro z hz
    exact ((differentiableAt_const (4 : ℂ)).div (branch_den_holomorphic a i z) hz).differentiableWithinAt
  · intro z hz
    have hf : DifferentiableAt ℂ (fun w : ℂ => a i + w^2) z := by fun_prop
    exact (hf.mul ((differentiableAt_const (4 : ℂ)).div
      (branch_den_holomorphic a i z) hz)).differentiableWithinAt

theorem branch_no_common_zero (a : Fin 4 → ℂ) (i : Fin 4) (z : ℂ)
    (hz : branchDen a i z ≠ 0) : branchQ0 a i z ≠ 0 :=
  div_ne_zero (by norm_num) hz

theorem infinity_den_zero (a : Fin 4 → ℂ) : infinityDen a 0 = 1 := by
  simp [infinityDen]

theorem infinity_holomorphic (a : Fin 4 → ℂ) :
    DifferentiableOn ℂ (infinityQ0 a) {z | infinityDen a z ≠ 0} ∧
    DifferentiableOn ℂ (infinityQ1 a) {z | infinityDen a z ≠ 0} := by
  constructor
  · intro z hz
    have hf : DifferentiableAt ℂ (fun w : ℂ => 4*w^2) z := by fun_prop
    exact (hf.div (infinity_den_holomorphic a z) hz).differentiableWithinAt
  · intro z hz
    exact ((differentiableAt_const (4 : ℂ)).div (infinity_den_holomorphic a z) hz).differentiableWithinAt

theorem infinity_no_common_zero (a : Fin 4 → ℂ) (z : ℂ) (hz : infinityDen a z ≠ 0) :
    infinityQ1 a z ≠ 0 := div_ne_zero (by norm_num) hz

theorem infinity_section_values (a : Fin 4 → ℂ) :
    infinityQ0 a 0 = 0 ∧ infinityQ1 a 0 = 4 := by
  simp [infinityQ0, infinityQ1, infinity_den_zero]

/-- An actual open neighborhood of every literal finite branch carries both
holomorphic sections, with the first nowhere zero. -/
theorem literal_branch_neighborhood (i : Fin 4) :
    ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
      DifferentiableOn ℂ (branchQ0 contacts i) U ∧
      DifferentiableOn ℂ (branchQ1 contacts i) U ∧
      ∀ z ∈ U, branchQ0 contacts i z ≠ 0 := by
  refine ⟨{z | branchDen contacts i z ≠ 0}, ?_, branch_den_nonzero contacts contacts_injective i,
    (branch_holomorphic contacts i).1, (branch_holomorphic contacts i).2, ?_⟩
  · exact isOpen_ne.preimage (branch_den_holomorphic contacts i).continuous
  · intro z hz
    exact branch_no_common_zero contacts i z hz

/-- The exact infinity transition has holomorphic sections on an actual
neighborhood, with the second nowhere zero including z=0. -/
theorem literal_infinity_neighborhood :
    ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
      DifferentiableOn ℂ (infinityQ0 contacts) U ∧
      DifferentiableOn ℂ (infinityQ1 contacts) U ∧
      ∀ z ∈ U, infinityQ1 contacts z ≠ 0 := by
  refine ⟨{z | infinityDen contacts z ≠ 0}, ?_, ?_,
    (infinity_holomorphic contacts).1, (infinity_holomorphic contacts).2, ?_⟩
  · exact isOpen_ne.preimage (infinity_den_holomorphic contacts).continuous
  · simp [infinity_den_zero]
  · intro z hz
    exact infinity_no_common_zero contacts z hz

end BicanonicalHolomorphy318
#print axioms BicanonicalHolomorphy318.source_holomorphic
#print axioms BicanonicalHolomorphy318.branch_holomorphic
#print axioms BicanonicalHolomorphy318.infinity_holomorphic
#print axioms BicanonicalHolomorphy318.literal_branch_neighborhood
#print axioms BicanonicalHolomorphy318.literal_infinity_neighborhood
