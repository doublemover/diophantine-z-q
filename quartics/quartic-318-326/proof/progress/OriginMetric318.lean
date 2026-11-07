module
public import QuadraticOrigin318
public section
noncomputable section
open Filter Set Finset CompactMetricComparison318 ConformalCurvature318
open QuadraticOrigin318 FiniteLaplacian318
open scoped Topology
namespace OriginMetric318
set_option maxHeartbeats 0
variable {ι:Type*} [Fintype ι]

@[expose] def normSquare (w:ℝ×ℝ) : ℝ := ‖complexCoord w‖^2
@[expose] def numerator (a:ℝ) (b c:ι→ℂ) (w:ℝ×ℝ) : ℝ :=
  a+normSquare w+∑i,quadraticDistance (b i) (c i) w
@[expose] def denominator (b c:ι→ℂ) (w:ℝ×ℝ) : ℝ :=
  ∏i,quadraticDistance (b i) (c i) w
@[expose] def metric (a:ℝ) (b c:ι→ℂ) (w:ℝ×ℝ) : ℝ :=
  4*numerator a b c w/denominator b c w

theorem normSquare_axes :
    (fun t:ℝ=>normSquare (t,0))=(fun t=>t^2) ∧
    (fun t:ℝ=>normSquare (0,t))=(fun t=>t^2) := by
  constructor <;> funext t <;> simp [normSquare,complexCoord,norm_mul]

theorem normSquare_axisC2 : AxisC2 normSquare := by
  constructor <;> simp only [normSquare_axes] <;> fun_prop

theorem normSquare_gradient : deriv (fun t=>normSquare (t,0)) 0=0 ∧
    deriv (fun t=>normSquare (0,t)) 0=0 := by
  rw [normSquare_axes.1,normSquare_axes.2]
  constructor <;> simpa using ((hasDerivAt_id (0:ℝ)).pow 2).deriv

theorem normSquare_laplacian : laplacianAtOrigin normSquare=4 := by
  unfold laplacianAtOrigin
  rw [normSquare_axes.1,normSquare_axes.2]
  have h:=quadratic_second_deriv (f:=fun t:ℝ=>t) 1 contDiffAt_id
  norm_num at h
  rw [h]
  norm_num

theorem numerator_axisC2 (a:ℝ) (b c:ι→ℂ) (hb:∀i,b i≠0) : AxisC2 (numerator a b c) := by
  constructor
  · exact (contDiffAt_const.add normSquare_axisC2.1).add
      (ContDiffAt.sum (fun i _=>(quadratic_axisC2 (b i) (c i) (hb i)).1))
  · exact (contDiffAt_const.add normSquare_axisC2.2).add
      (ContDiffAt.sum (fun i _=>(quadratic_axisC2 (b i) (c i) (hb i)).2))

theorem numerator_zero (a:ℝ) (b c:ι→ℂ) : numerator a b c (0,0)=a+∑i,‖b i‖ := by
  simp [numerator,normSquare,quadraticDistance,complexCoord]

theorem denominator_zero (b c:ι→ℂ) : denominator b c (0,0)=∏i,‖b i‖ := by
  simp [denominator,quadraticDistance,complexCoord]

theorem numerator_gradient (a:ℝ) (b c:ι→ℂ) (hb:∀i,b i≠0) :
    gradientSq (numerator a b c)=0 := by
  have hx:deriv (fun t=>numerator a b c (t,0)) 0=0 := by
    unfold numerator
    rw [deriv_fun_add ((contDiffAt_const.add normSquare_axisC2.1).differentiableAt (by norm_num))
      ((ContDiffAt.sum (fun i _=>(quadratic_axisC2 (b i) (c i) (hb i)).1)).differentiableAt (by norm_num))]
    rw [deriv_const_add',normSquare_gradient.1,deriv_fun_sum (fun i _=>
      ((quadratic_axisC2 (b i) (c i) (hb i)).1).differentiableAt (by norm_num))]
    simp_rw [(quadratic_gradient _ _ (hb _)).1]
    simp
  have hy:deriv (fun t=>numerator a b c (0,t)) 0=0 := by
    unfold numerator
    rw [deriv_fun_add ((contDiffAt_const.add normSquare_axisC2.2).differentiableAt (by norm_num))
      ((ContDiffAt.sum (fun i _=>(quadratic_axisC2 (b i) (c i) (hb i)).2)).differentiableAt (by norm_num))]
    rw [deriv_const_add',normSquare_gradient.2,deriv_fun_sum (fun i _=>
      ((quadratic_axisC2 (b i) (c i) (hb i)).2).differentiableAt (by norm_num))]
    simp_rw [(quadratic_gradient _ _ (hb _)).2]
    simp
  simp only [gradientSq,hx,hy,zero_pow (by decide:2≠0),add_zero]

theorem numerator_laplacian (a:ℝ) (b c:ι→ℂ) (hb:∀i,b i≠0) :
    laplacianAtOrigin (numerator a b c)=4 := by
  have he:numerator a b c=(fun w=>a+(normSquare w+∑i,quadraticDistance (b i) (c i) w)) := by
    funext w; unfold numerator; ring
  rw [he,laplacian_const_add]
  have hs:AxisC2 (fun w=>∑i,quadraticDistance (b i) (c i) w) :=
    ⟨ContDiffAt.sum (fun i _=>(quadratic_axisC2 (b i) (c i) (hb i)).1),
     ContDiffAt.sum (fun i _=>(quadratic_axisC2 (b i) (c i) (hb i)).2)⟩
  have hadd:laplacianAtOrigin (fun w=>normSquare w+∑i,quadraticDistance (b i) (c i) w)=
      laplacianAtOrigin normSquare+laplacianAtOrigin (fun w=>∑i,quadraticDistance (b i) (c i) w) := by
    unfold laplacianAtOrigin
    have add2 {f g:ℝ→ℝ} (hf:ContDiffAt ℝ 2 f 0) (hg:ContDiffAt ℝ 2 g 0) :
        deriv (deriv (fun t=>f t+g t)) 0=deriv (deriv f) 0+deriv (deriv g) 0 := by
      have hh:=second_deriv_sum (fun i:Fin 2=>![f,g] i) 0 (by
        intro i; fin_cases i
        · exact hf
        · exact hg)
      simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
    rw [add2 normSquare_axisC2.1 hs.1,add2 normSquare_axisC2.2 hs.2]
    ring
  rw [hadd,normSquare_laplacian,laplacian_sum _ (fun i=>quadratic_axisC2 _ _ (hb i))]
  simp_rw [quadratic_laplacian _ _ (hb _)]
  simp


theorem log_quadratic_laplacian (b c:ℂ) (hb:b≠0) :
    laplacianAtOrigin (fun w=>Real.log (quadraticDistance b c w))=0 := by
  have hq:quadraticDistance b c (0,0)≠0 := by
    simpa [quadraticDistance,complexCoord] using norm_ne_zero_iff.mpr hb
  rw [laplacian_log _ (quadratic_axisC2 b c hb) hq,quadratic_laplacian _ _ hb]
  simp only [gradientSq,(quadratic_gradient b c hb).1,(quadratic_gradient b c hb).2]
  simp

theorem log_metric_eventually (a:ℝ) (b c:ι→ℂ) (hb:∀i,b i≠0)
    (ha:0<a+∑i,‖b i‖) :
    (fun w=>Real.log (metric a b c w))=ᶠ[𝓝 (0,0)]
      (fun w=>Real.log 4+Real.log (numerator a b c w)-
        ∑i,Real.log (quadraticDistance (b i) (c i) w)) := by
  have hn:ContinuousAt (numerator a b c) (0,0) := by
    unfold numerator normSquare quadraticDistance complexCoord
    fun_prop
  have hp:∀ᶠ w in 𝓝 (0,0),0<numerator a b c w :=
    hn.eventually (eventually_gt_nhds (by rwa [numerator_zero]))
  have hq:∀ᶠ w:ℝ×ℝ in 𝓝 (0,0),∀i,0<quadraticDistance (b i) (c i) w := by
    apply Filter.eventually_all.mpr
    intro i
    have hc:ContinuousAt (quadraticDistance (b i) (c i)) (0,0) := by
      unfold quadraticDistance complexCoord
      fun_prop
    exact hc.eventually (eventually_gt_nhds (by
      simpa [quadraticDistance,complexCoord] using norm_pos_iff.mpr (hb i)))
  filter_upwards [hp,hq] with w hw hwi
  have hd:denominator b c w≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>(hwi i).ne')
  rw [metric,Real.log_div (mul_pos (by norm_num) hw).ne' hd,
    Real.log_mul (by norm_num) hw.ne',denominator,Real.log_prod (fun i _=>(hwi i).ne')]

theorem log_metric_laplacian (a:ℝ) (b c:ι→ℂ) (hb:∀i,b i≠0)
    (ha:0<a+∑i,‖b i‖) :
    laplacianAtOrigin (fun w=>Real.log (metric a b c w))=4/(a+∑i,‖b i‖) := by
  have hn:numerator a b c (0,0)≠0:=by rw[numerator_zero]; exact ha.ne'
  have hl (i:ι) : AxisC2 (fun w=>Real.log (quadraticDistance (b i) (c i) w)) := by
    have hq:quadraticDistance (b i) (c i) (0,0)≠0 := by
      simpa [quadraticDistance,complexCoord] using norm_ne_zero_iff.mpr (hb i)
    exact ⟨((quadratic_axisC2 _ _ (hb i)).1).log hq,((quadratic_axisC2 _ _ (hb i)).2).log hq⟩
  have hs:AxisC2 (fun w=>∑i,Real.log (quadraticDistance (b i) (c i) w)) :=
    ⟨ContDiffAt.sum (fun i _=>(hl i).1),ContDiffAt.sum (fun i _=>(hl i).2)⟩
  have hnc:AxisC2 (fun w=>Real.log 4+Real.log (numerator a b c w)) :=
    ⟨contDiffAt_const.add (((numerator_axisC2 a b c hb).1).log hn),
     contDiffAt_const.add (((numerator_axisC2 a b c hb).2).log hn)⟩
  rw [laplacian_congr (log_metric_eventually a b c hb ha),laplacian_sub _ _ hnc hs,
    laplacian_const_add,laplacian_sum _ hl]
  simp_rw [log_quadratic_laplacian _ _ (hb _)]
  rw [Finset.sum_const_zero,sub_zero,laplacian_log _ (numerator_axisC2 a b c hb) hn,
    numerator_laplacian a b c hb,numerator_gradient a b c hb,numerator_zero]
  field_simp
  ring

theorem curvature_exact (a:ℝ) (b c:ι→ℂ) (hb:∀i,b i≠0)
    (ha:0<a+∑i,‖b i‖) :
    curvature (metric a b c)=-(∏i,‖b i‖)/(2*(a+∑i,‖b i‖)^2) := by
  rw [curvature,log_metric_laplacian a b c hb ha,metric,numerator_zero,denominator_zero]
  have hp:(∏i,‖b i‖)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>norm_ne_zero_iff.mpr (hb i))
  field_simp

end OriginMetric318
#print axioms OriginMetric318.numerator_laplacian

#print axioms OriginMetric318.curvature_exact
