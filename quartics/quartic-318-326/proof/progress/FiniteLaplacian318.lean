module
public import DistanceLaplacian318
public section
noncomputable section
open Filter Set Finset CompactMetricComparison318 ConformalCurvature318
open scoped Topology
namespace FiniteLaplacian318
set_option maxHeartbeats 0

@[expose] def gradientSq (f:ℝ×ℝ→ℝ) : ℝ :=
  (deriv (fun t=>f (t,0)) 0)^2+(deriv (fun t=>f (0,t)) 0)^2

theorem second_deriv_log {f:ℝ→ℝ} {x:ℝ} (hf:ContDiffAt ℝ 2 f x) (hf0:f x≠0) :
    deriv (deriv (fun t=>Real.log (f t))) x=
      (deriv (deriv f) x*f x-(deriv f x)^2)/(f x)^2 := by
  have hp:∀ᶠ t in 𝓝 x,f t≠0:=hf.continuousAt.eventually_ne hf0
  have he:deriv (fun t=>Real.log (f t)) =ᶠ[𝓝 x] (fun t=>deriv f t/f t) := by
    filter_upwards [hf.eventually (by norm_num),hp] with t ht ht0
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.log ht0).deriv
  rw [he.deriv_eq]
  have hd:=((hf.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt.div
    (hf.differentiableAt (by norm_num)).hasDerivAt hf0
  change HasDerivAt (fun t=>deriv f t/f t) _ _ at hd
  rw [hd.deriv]
  ring

theorem second_deriv_sum {ι:Type*} [Fintype ι] (f:ι→ℝ→ℝ) (x:ℝ)
    (hf:∀i,ContDiffAt ℝ 2 (f i) x) :
    deriv (deriv (fun t=>∑i,f i t)) x=∑i,deriv (deriv (f i)) x := by
  have hevent:∀ᶠ t in 𝓝 x,∀i,ContDiffAt ℝ 2 (f i) t :=
    Filter.eventually_all.mpr (fun i=>(hf i).eventually (by norm_num))
  have he:deriv (fun t=>∑i,f i t) =ᶠ[𝓝 x] (fun t=>∑i,deriv (f i) t) := by
    filter_upwards [hevent] with t ht
    exact deriv_fun_sum (fun i _=>(ht i).differentiableAt (by norm_num))
  rw [he.deriv_eq]
  exact deriv_fun_sum (fun i _=>((hf i).derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num))

theorem laplacian_sum {ι:Type*} [Fintype ι] (f:ι→ℝ×ℝ→ℝ) (hf:∀i,AxisC2 (f i)) :
    laplacianAtOrigin (fun z=>∑i,f i z)=∑i,laplacianAtOrigin (f i) := by
  unfold laplacianAtOrigin
  rw [second_deriv_sum _ _ (fun i=>(hf i).1),second_deriv_sum _ _ (fun i=>(hf i).2)]
  exact Finset.sum_add_distrib.symm

theorem laplacian_sub (f g:ℝ×ℝ→ℝ) (hf:AxisC2 f) (hg:AxisC2 g) :
    laplacianAtOrigin (fun z=>f z-g z)=laplacianAtOrigin f-laplacianAtOrigin g := by
  unfold laplacianAtOrigin
  rw [ConformalCurvature318.second_deriv_sub hf.1 hg.1,
    ConformalCurvature318.second_deriv_sub hf.2 hg.2]
  ring

theorem laplacian_const_add (c:ℝ) (f:ℝ×ℝ→ℝ) :
    laplacianAtOrigin (fun z=>c+f z)=laplacianAtOrigin f := by
  simp only [laplacianAtOrigin,deriv_const_add']

theorem laplacian_log (f:ℝ×ℝ→ℝ) (hf:AxisC2 f) (hf0:f (0,0)≠0) :
    laplacianAtOrigin (fun z=>Real.log (f z))=
      (laplacianAtOrigin f*f (0,0)-gradientSq f)/(f (0,0))^2 := by
  unfold laplacianAtOrigin gradientSq
  rw [second_deriv_log hf.1 hf0,second_deriv_log hf.2 hf0]
  ring

theorem laplacian_congr {f g:ℝ×ℝ→ℝ} (h:f=ᶠ[𝓝 (0,0)]g) :
    laplacianAtOrigin f=laplacianAtOrigin g := by
  have hx:ContinuousAt (fun t:ℝ=>(t,(0:ℝ))) 0 := by fun_prop
  have hy:ContinuousAt (fun t:ℝ=>((0:ℝ),t)) 0 := by fun_prop
  have heX:=h.comp_tendsto hx.tendsto
  have heY:=h.comp_tendsto hy.tendsto
  exact congrArg₂ (·+·) heX.deriv.deriv_eq heY.deriv.deriv_eq

end FiniteLaplacian318
#print axioms FiniteLaplacian318.laplacian_log
#print axioms FiniteLaplacian318.laplacian_sum
