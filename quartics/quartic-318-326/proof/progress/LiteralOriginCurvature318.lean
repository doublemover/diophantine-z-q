module
public import OriginMetric318
public section
noncomputable section
open Finset CompactMetricComparison318 ConformalCurvature318
open QuadraticOrigin318 MetricSmoothExtension318 LiteralMetricExtension318
namespace LiteralOriginCurvature318
set_option maxHeartbeats 0

/-- Exact computed curvature at a finite branch, with genuine norm coefficients. -/
theorem branch_curvature {ι:Type*} [Fintype ι] (b:ι→ℂ) (hb:∀i,b i≠0) :
    curvature (fun w:ℝ×ℝ=>branchCoefficient b (complexCoord w))=
      -(∏i,‖b i‖)/(2*(1+∑i,‖b i‖)^2) := by
  have he:(fun w:ℝ×ℝ=>branchCoefficient b (complexCoord w))=
      OriginMetric318.metric 1 b (fun _=>1) := by
    funext w
    simp [branchCoefficient,OriginMetric318.metric,OriginMetric318.numerator,
      OriginMetric318.denominator,OriginMetric318.normSquare,quadraticDistance]
  rw [he]
  apply OriginMetric318.curvature_exact _ _ _ hb
  have hsum:0≤∑i,‖b i‖:=Finset.sum_nonneg (fun i _=>norm_nonneg _)
  linarith

/-- The actual infinity coefficient has curvature exactly minus one thirty-second. -/
theorem infinity_curvature (a:Fin 4→ℂ) :
    curvature (fun w:ℝ×ℝ=>infinityCoefficient a (complexCoord w))=-(1:ℝ)/32 := by
  have he:(fun w:ℝ×ℝ=>infinityCoefficient a (complexCoord w))=
      OriginMetric318.metric 0 (fun _ : Fin 4=>1) (fun i=>-a i) := by
    funext w
    simp only [infinityCoefficient,OriginMetric318.metric,OriginMetric318.numerator,
      OriginMetric318.denominator,OriginMetric318.normSquare,quadraticDistance,zero_add,
      neg_mul,sub_eq_add_neg]
  rw [he,OriginMetric318.curvature_exact _ _ _ (fun _=>by norm_num) (by norm_num)]
  norm_num

/-- Distinct finite source contacts have distance at least one and at most twice
76832. The conservative latter bound suffices for the actual origin curvature. -/
theorem branch_distance_bounds (i:Fin 4) (j:{j:Fin 4 // j≠i}) :
    1≤‖contacts i-contacts j‖ ∧ ‖contacts i-contacts j‖≤153664 := by
  have h1:=FiveContactMetricBounds318.contact_separation i j (Ne.symm j.property)
  have hu:=norm_sub_le (contacts i) (contacts j)
  have hi:=FiveContactMetricBounds318.contact_norm i
  have hj:=FiveContactMetricBounds318.contact_norm j
  rw [LiteralCurvature318.contacts_eq] at h1 hi hj
  rw [dist_eq_norm] at h1
  exact ⟨h1,by linarith⟩

theorem finite_branch_curvature_bound (i:Fin 4) :
    curvature (fun w:ℝ×ℝ=>branchCoefficient
      (fun j:{j:Fin 4 // j≠i}=>contacts i-contacts j) (complexCoord w))≤
      -(12540153541944538512:ℝ)⁻¹ := by
  let b : {j:Fin 4 // j≠i}→ℂ := fun j=>contacts i-contacts j
  have hb:∀j,b j≠0:=fun j=>sub_ne_zero.mpr (contacts_injective.ne (Ne.symm j.property))
  have hn:0<1+∑j,‖b j‖ := by positivity
  have hc:Fintype.card {j:Fin 4 // j≠i}=3 := by simp
  have hu:1+∑j,‖b j‖≤460993 := by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>(branch_distance_bounds i j).2)
    change (∑j,‖b j‖)≤∑_j:{j:Fin 4 // j≠i},(153664:ℝ) at hh
    norm_num [hc] at hh
    linarith
  have hp:1≤∏j,‖b j‖:=Finset.one_le_prod₀ (fun j _=>(branch_distance_bounds i j).1)
  have hpow: (1+∑j,‖b j‖)^2≤(460993:ℝ)^2:=pow_le_pow_left₀ hn.le hu 2
  have hbound:(12540153541944538512:ℝ)⁻¹≤(∏j,‖b j‖)/(2*(1+∑j,‖b j‖)^2) := by
    apply (le_div_iff₀ (show 0<2*(1+∑j,‖b j‖)^2 by positivity)).mpr
    norm_num at hpow ⊢
    nlinarith
  change curvature (fun w:ℝ×ℝ=>branchCoefficient b (complexCoord w))≤_
  rw [branch_curvature b hb]
  simpa only [neg_div] using neg_le_neg hbound

theorem infinity_curvature_bound :
    curvature (fun w:ℝ×ℝ=>infinityCoefficient contacts (complexCoord w))≤
      -(12540153541944538512:ℝ)⁻¹ := by
  rw [infinity_curvature]
  norm_num
end LiteralOriginCurvature318
#print axioms LiteralOriginCurvature318.finite_branch_curvature_bound
#print axioms LiteralOriginCurvature318.infinity_curvature_bound
