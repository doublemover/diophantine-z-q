module
public import SourceMetricCharts318
public import BicanonicalHolomorphy318
public section
noncomputable section
open Finset MetricSmoothExtension318 MetricPullback318 LiteralMetricExtension318
open BicanonicalCharts318 SourceMetricCharts318
namespace SectionCoefficientBounds318
set_option maxHeartbeats 0

@[expose] def Chart.section0 : Chart→ℂ
  | .regular z _ => q0 contacts z
  | .finiteBranch i => branchQ0 contacts i 0
  | .infinity => infinityQ0 contacts 0
@[expose] def Chart.section1 : Chart→ℂ
  | .regular z _ => q1 contacts z
  | .finiteBranch i => branchQ1 contacts i 0
  | .infinity => infinityQ1 contacts 0

theorem norm_le_sum_distances (z:ℂ) : ‖z‖≤∑j:Fin 4,‖z-contacts j‖ := by
  have hh:=Finset.single_le_sum (s:=Finset.univ) (f:=fun j:Fin 4=>‖z-contacts j‖)
    (fun j _=>norm_nonneg _) (Finset.mem_univ (0:Fin 4))
  simpa [contacts] using hh

theorem regular_coefficient_bounds (z:ℂ) (hz:∀i:Fin 4,z≠contacts i) :
    ‖q0 contacts z‖≤sourceCoefficient contacts z ∧
    ‖q1 contacts z‖≤sourceCoefficient contacts z := by
  have hp:0<∏j:Fin 4,‖z-contacts j‖:=Finset.prod_pos (fun j _=>norm_pos_iff.mpr (sub_ne_zero.mpr (hz j)))
  have hs:0≤∑j:Fin 4,‖z-contacts j‖:=Finset.sum_nonneg (fun j _=>norm_nonneg _)
  have hzU:=norm_le_sum_distances z
  constructor
  · simp only [q0,contactPolynomial,norm_div,norm_one,norm_prod,sourceCoefficient]
    apply div_le_div_of_nonneg_right (by linarith) hp.le
  · simp only [q1,q0,contactPolynomial,norm_mul,norm_div,norm_one,norm_prod,sourceCoefficient]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hp.le

theorem branch_contact_bound (i:Fin 4) :
    ‖contacts i‖≤1+∑j:{j:Fin 4 // j≠i},‖contacts i-contacts j‖ := by
  have hs:0≤∑j:{j:Fin 4 // j≠i},‖contacts i-contacts j‖:=
    Finset.sum_nonneg (fun j _=>norm_nonneg _)
  by_cases hi:i=0
  · subst i
    simp only [contacts,Matrix.cons_val_zero,norm_zero]
    positivity
  · let j0:{j:Fin 4 // j≠i}:=⟨0,Ne.symm hi⟩
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j:{j:Fin 4 // j≠i}=>‖contacts i-contacts j‖)
      (fun j _=>norm_nonneg _) (Finset.mem_univ j0)
    have hzero:contacts j0=0:=rfl
    rw [hzero,sub_zero] at hh
    linarith

theorem branch_coefficient_bounds (i:Fin 4) :
    ‖branchQ0 contacts i 0‖≤branchCoefficient (fun j:{j:Fin 4 // j≠i}=>contacts i-contacts j) 0 ∧
    ‖branchQ1 contacts i 0‖≤branchCoefficient (fun j:{j:Fin 4 // j≠i}=>contacts i-contacts j) 0 := by
  have hp:0<∏j:{j:Fin 4 // j≠i},‖contacts i-contacts j‖:=
    Finset.prod_pos (fun j _=>norm_pos_iff.mpr (sub_ne_zero.mpr (contacts_injective.ne (Ne.symm j.property))))
  have hs:0≤∑j:{j:Fin 4 // j≠i},‖contacts i-contacts j‖:=Finset.sum_nonneg (fun j _=>norm_nonneg _)
  have hi:=branch_contact_bound i
  constructor
  · simp only [branchQ0,branchDen,branchCoefficient,zero_pow (by decide:2≠0),add_zero,
      norm_div,Complex.norm_ofNat,norm_prod,norm_zero]
    apply div_le_div_of_nonneg_right (by linarith) hp.le
  · simp only [branchQ1,branchQ0,branchDen,branchCoefficient,zero_pow (by decide:2≠0),add_zero,
      norm_mul,norm_div,Complex.norm_ofNat,norm_prod,norm_zero]
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right (by nlinarith) hp.le

theorem Chart.coefficient_bounds (c:Chart) :
    ‖Chart.section0 c‖≤c.coefficient (0,0) ∧ ‖Chart.section1 c‖≤c.coefficient (0,0) := by
  cases c with
  | regular z hz =>
    simpa [Chart.section0,Chart.section1,SourceMetricCharts318.Chart.coefficient,
      QuadraticOrigin318.complexCoord] using regular_coefficient_bounds z hz
  | finiteBranch i =>
    simpa [Chart.section0,Chart.section1,SourceMetricCharts318.Chart.coefficient,
      QuadraticOrigin318.complexCoord] using branch_coefficient_bounds i
  | infinity =>
    norm_num [Chart.section0,Chart.section1,SourceMetricCharts318.Chart.coefficient,
      QuadraticOrigin318.complexCoord,infinityCoefficient_zero,infinityQ0,infinityQ1,
      BicanonicalHolomorphy318.infinity_den_zero]

end SectionCoefficientBounds318
#print axioms SectionCoefficientBounds318.Chart.coefficient_bounds
