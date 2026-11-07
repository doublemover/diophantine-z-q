module
public import ConformalCurvature318
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
open Filter Set CompactMetricComparison318
open scoped Topology
namespace DistanceLaplacian318
set_option maxHeartbeats 0

@[expose] def radius (x y:ℝ) : ℝ := Real.sqrt (x^2+y^2)

theorem radius_sq (x y:ℝ) : radius x y ^2=x^2+y^2 :=
  Real.sq_sqrt (by positivity)

theorem radius_pos {x y:ℝ} (h:0<x^2+y^2) : 0<radius x y := Real.sqrt_pos.mpr h

theorem radius_symm (x y:ℝ) : radius x y=radius y x := by simp [radius,add_comm]

theorem radius_complex (z:ℂ) : radius z.re z.im=‖z‖ := by
  rw [radius,Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply,pow_two]

theorem line_contDiff {x y:ℝ} (h:0<x^2+y^2) :
    ContDiffAt ℝ 2 (fun t:ℝ=>radius (x+t) y) 0 := by
  apply ContDiffAt.sqrt (by fun_prop)
  simpa using h.ne'

/-- First derivative of the actual translated Euclidean distance. -/
theorem hasDerivAt_line (x y t:ℝ) (h:0<(x+t)^2+y^2) :
    HasDerivAt (fun s:ℝ=>radius (x+s) y)
      ((x+t)/radius (x+t) y) t := by
  have ha:HasDerivAt (fun s:ℝ=>(x+s)^2+y^2) (2*(x+t)) t := by
    convert (((hasDerivAt_const t x).add (hasDerivAt_id t)).pow 2).add_const (y^2) using 1 <;> simp only [Pi.add_apply,Pi.pow_apply,id_eq,zero_add,add_zero,pow_one,mul_one] <;> ring
  convert ha.sqrt h.ne' using 1 <;> simp only [radius] <;> field_simp <;> ring

/-- The actual second derivative equals the transverse squared distance
normalized by the cubed radius. -/
theorem second_deriv_line (x y:ℝ) (h:0<x^2+y^2) :
    deriv (deriv (fun t:ℝ=>radius (x+t) y)) 0=y^2/(radius x y)^3 := by
  have hc:ContinuousAt (fun t:ℝ=>(x+t)^2+y^2) 0 := by fun_prop
  have hp:∀ᶠ t in 𝓝 (0:ℝ),0<(x+t)^2+y^2 := hc.eventually (eventually_gt_nhds (by simpa using h))
  have he : deriv (fun t:ℝ=>radius (x+t) y) =ᶠ[𝓝 (0:ℝ)] (fun t=>(x+t)/radius (x+t) y) := by
    filter_upwards [hp] with t ht
    exact (hasDerivAt_line x y t ht).deriv
  rw [he.deriv_eq]
  have hd:=((hasDerivAt_const 0 x).add (hasDerivAt_id 0)).div
    (hasDerivAt_line x y 0 (by simpa using h)) (by simpa using (radius_pos h).ne')
  simp only [Pi.add_apply,Pi.div_apply,id_eq] at hd
  change HasDerivAt (fun t:ℝ=>(x+t)/radius (x+t) y) _ _ at hd
  rw [hd.deriv]
  simp only [add_zero,zero_add,one_mul]
  have hr:radius x y≠0:=(radius_pos h).ne'
  have hs:=radius_sq x y
  field_simp
  nlinarith

/-- First derivative of the actual logarithmic distance. -/
theorem hasDerivAt_log_line (x y t:ℝ) (h:0<(x+t)^2+y^2) :
    HasDerivAt (fun s:ℝ=>Real.log (radius (x+s) y))
      ((x+t)/((x+t)^2+y^2)) t := by
  have hd:=(hasDerivAt_line x y t h).log (radius_pos h).ne'
  convert hd using 1
  have hs:=radius_sq (x+t) y
  have hr:radius (x+t) y≠0:=(radius_pos h).ne'
  field_simp
  rw [hs]

theorem second_deriv_log_line (x y:ℝ) (h:0<x^2+y^2) :
    deriv (deriv (fun t:ℝ=>Real.log (radius (x+t) y))) 0=
      (y^2-x^2)/(x^2+y^2)^2 := by
  have hc:ContinuousAt (fun t:ℝ=>(x+t)^2+y^2) 0 := by fun_prop
  have hp:∀ᶠ t in 𝓝 (0:ℝ),0<(x+t)^2+y^2 := hc.eventually (eventually_gt_nhds (by simpa using h))
  have he : deriv (fun t:ℝ=>Real.log (radius (x+t) y)) =ᶠ[𝓝 (0:ℝ)]
      (fun t=>(x+t)/((x+t)^2+y^2)) := by
    filter_upwards [hp] with t ht
    exact (hasDerivAt_log_line x y t ht).deriv
  rw [he.deriv_eq]
  have ha:HasDerivAt (fun s:ℝ=>(x+s)^2+y^2) (2*x) 0 := by
    convert (((hasDerivAt_const 0 x).add (hasDerivAt_id 0)).pow 2).add_const (y^2) using 1 <;> simp only [Pi.add_apply,Pi.pow_apply,id_eq,zero_add,add_zero,pow_one,mul_one] <;> ring
  have hd:=((hasDerivAt_const 0 x).add (hasDerivAt_id 0)).div ha (by simpa using h.ne')
  simp only [Pi.add_apply,Pi.div_apply,id_eq] at hd
  change HasDerivAt (fun t:ℝ=>(x+t)/((x+t)^2+y^2)) _ _ at hd
  rw [hd.deriv]
  simp only [add_zero,zero_add,one_mul]
  ring

@[expose] def translated (x y:ℝ) (w:ℝ×ℝ) : ℝ := radius (x+w.1) (y+w.2)

theorem translated_axisC2 (x y:ℝ) (h:0<x^2+y^2) :
    ConformalCurvature318.AxisC2 (translated x y) := by
  constructor
  · simpa only [translated,add_zero] using line_contDiff h
  · simpa only [translated,add_zero,radius_symm] using line_contDiff (x:=y) (y:=x) (by nlinarith :0<y^2+x^2)

/-- The ordinary area Laplacian of distance is the inverse radius. -/
theorem laplacian_radius (x y:ℝ) (h:0<x^2+y^2) :
    laplacianAtOrigin (translated x y)=(radius x y)⁻¹ := by
  unfold laplacianAtOrigin
  simp only [translated,add_zero]
  have hy : (fun t:ℝ=>radius x (y+t))=(fun t=>radius (y+t) x) := by
    funext t;exact radius_symm _ _
  rw [hy,second_deriv_line x y h,second_deriv_line y x (by nlinarith),radius_symm y x]
  have hs:=radius_sq x y
  have hr:radius x y≠0:=(radius_pos h).ne'
  field_simp
  nlinarith

/-- Logarithmic Euclidean distance is harmonic away from its contact. -/
theorem laplacian_log_radius (x y:ℝ) (h:0<x^2+y^2) :
    laplacianAtOrigin (fun w=>Real.log (translated x y w))=0 := by
  unfold laplacianAtOrigin
  simp only [translated,add_zero]
  have hy : (fun t:ℝ=>Real.log (radius x (y+t)))=(fun t=>Real.log (radius (y+t) x)) := by
    funext t;rw [radius_symm]
  rw [hy,second_deriv_log_line x y h,second_deriv_log_line y x (by nlinarith)]
  rw [add_comm (y^2) (x^2)]
  ring

end DistanceLaplacian318
#print axioms DistanceLaplacian318.laplacian_radius
#print axioms DistanceLaplacian318.laplacian_log_radius
