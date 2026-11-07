module
public import FiniteLaplacian318
public section
noncomputable section
open Filter Set Finset CompactMetricComparison318 ConformalCurvature318
open DistanceLaplacian318 FiniteLaplacian318
open scoped Topology
namespace ContactCurvature318
set_option maxHeartbeats 0
variable {ι:Type*} [Fintype ι]

@[expose] def total (x y:ι→ℝ) (w:ℝ×ℝ) : ℝ :=
  1+∑i,translated (x i) (y i) w

@[expose] def product (x y:ι→ℝ) (w:ℝ×ℝ) : ℝ :=
  ∏i,translated (x i) (y i) w

@[expose] def metric (x y:ι→ℝ) (w:ℝ×ℝ) : ℝ := total x y w/product x y w

theorem total_pos (x y:ι→ℝ) (w:ℝ×ℝ) : 0<total x y w := by
  have hs:0≤∑i,translated (x i) (y i) w :=
    Finset.sum_nonneg (fun i _=>Real.sqrt_nonneg _)
  unfold total
  linarith

theorem total_axisC2 (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) : AxisC2 (total x y) := by
  constructor
  · exact contDiffAt_const.add (ContDiffAt.sum (fun i _=>(translated_axisC2 _ _ (h i)).1))
  · exact contDiffAt_const.add (ContDiffAt.sum (fun i _=>(translated_axisC2 _ _ (h i)).2))

theorem metric_axisC2 (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) : AxisC2 (metric x y) := by
  have hp:product x y (0,0)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    simpa [translated] using (radius_pos (h i)).ne'
  constructor
  · exact (total_axisC2 x y h).1.div
      (contDiffAt_prod (fun i _=>(translated_axisC2 _ _ (h i)).1)) hp
  · exact (total_axisC2 x y h).2.div
      (contDiffAt_prod (fun i _=>(translated_axisC2 _ _ (h i)).2)) hp

theorem laplacian_total (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    laplacianAtOrigin (total x y)=∑i,(radius (x i) (y i))⁻¹ := by
  change laplacianAtOrigin (fun w=>1+∑i,translated (x i) (y i) w)=_
  rw [laplacian_const_add,laplacian_sum _ (fun i=>translated_axisC2 _ _ (h i))]
  exact Finset.sum_congr rfl (fun i _=>laplacian_radius _ _ (h i))

theorem log_metric_eventually (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    (fun w=>Real.log (metric x y w)) =ᶠ[𝓝 (0,0)]
      (fun w=>Real.log (total x y w)-∑i,Real.log (translated (x i) (y i) w)) := by
  have hp:∀ᶠ w:ℝ×ℝ in 𝓝 (0,0),∀i,0<translated (x i) (y i) w := by
    apply Filter.eventually_all.mpr
    intro i
    have hc:ContinuousAt (translated (x i) (y i)) (0,0) := by
      unfold translated radius
      fun_prop
    exact hc.eventually (eventually_gt_nhds (by simpa [translated] using radius_pos (h i)))
  filter_upwards [hp] with w hw
  have hprod:product x y w≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>(hw i).ne')
  rw [metric,Real.log_div (total_pos x y w).ne' hprod,product,
    Real.log_prod (fun i _=>(hw i).ne')]

theorem laplacian_log_metric (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    laplacianAtOrigin (fun w=>Real.log (metric x y w))=
      ((∑i,(radius (x i) (y i))⁻¹)*total x y (0,0)-gradientSq (total x y))/(total x y (0,0))^2 := by
  have hs:AxisC2 (fun w=>∑i,Real.log (translated (x i) (y i) w)) := by
    constructor
    · exact ContDiffAt.sum (fun i _=>((translated_axisC2 _ _ (h i)).1).log
        (by simpa [translated] using (radius_pos (h i)).ne'))
    · exact ContDiffAt.sum (fun i _=>((translated_axisC2 _ _ (h i)).2).log
        (by simpa [translated] using (radius_pos (h i)).ne'))
  have hl (i:ι) : AxisC2 (fun w=>Real.log (translated (x i) (y i) w)) :=
    ⟨((translated_axisC2 _ _ (h i)).1).log (by simpa [translated] using (radius_pos (h i)).ne'),
     ((translated_axisC2 _ _ (h i)).2).log (by simpa [translated] using (radius_pos (h i)).ne')⟩
  rw [laplacian_congr (log_metric_eventually x y h),
    laplacian_sub _ _ ⟨((total_axisC2 x y h).1).log (total_pos x y (0,0)).ne',
      ((total_axisC2 x y h).2).log (total_pos x y (0,0)).ne'⟩ hs,
    laplacian_sum _ hl]
  simp_rw [laplacian_log_radius _ _ (h _)]
  rw [Finset.sum_const_zero,sub_zero,laplacian_log _ (total_axisC2 x y h) (total_pos x y (0,0)).ne',
    laplacian_total x y h]

/-- Actual conformal curvature of the finite-contact distance metric. Every
differential term is computed from the literal metric coefficient. -/
theorem negative_curvature (x y:ι→ℝ) (h:∀i,0<(x i)^2+(y i)^2) :
    -ConformalCurvature318.curvature (metric x y)=
      (∏i,radius (x i) (y i))/(2*(total x y (0,0))^3)*
        (total x y (0,0)*(∑i,(radius (x i) (y i))⁻¹)-gradientSq (total x y)) := by
  rw [ConformalCurvature318.curvature,laplacian_log_metric x y h]
  have ht:total x y (0,0)≠0:=(total_pos x y (0,0)).ne'
  have hp:(∏i,radius (x i) (y i))≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>(radius_pos (h i)).ne')
  simp only [metric,product,translated,add_zero]
  field_simp

end ContactCurvature318
#print axioms ContactCurvature318.negative_curvature
