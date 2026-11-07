module
public import HarmonicAxis318
public section
noncomputable section
open Filter Set CompactMetricComparison318 ConformalCurvature318 FiniteLaplacian318
open HarmonicAxis318
namespace ImaginaryGradient318
set_option maxHeartbeats 0

theorem derivative_x (f:ℂ→ℂ) (hf:DifferentiableAt ℂ f 0) :
    deriv (fun t:ℝ=>(f (t:ℂ)).im) 0=(deriv f 0).im := by
  have hd:HasDerivAt (fun t:ℝ=>f (t:ℂ)) (deriv f 0) 0:=hf.hasDerivAt.comp_ofReal
  have hh:=Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  change HasDerivAt (fun t:ℝ=>(f (t:ℂ)).im) _ _ at hh
  exact hh.deriv

theorem derivative_y (f:ℂ→ℂ) (hf:DifferentiableAt ℂ f 0) :
    deriv (fun t:ℝ=>(f ((t:ℂ)*Complex.I)).im) 0=(deriv f 0).re := by
  have hf':HasDerivAt f (deriv f 0) ((0:ℂ)*Complex.I):=by simpa using hf.hasDerivAt
  have hd:=hf'.comp 0 ((hasDerivAt_id (0:ℂ)).mul_const Complex.I)
  have hr:=hd.comp_ofReal
  have hh:=Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hr
  change HasDerivAt (fun t:ℝ=>(f ((t:ℂ)*Complex.I)).im) _ _ at hh
  simpa using hh.deriv

/-- The actual Cauchy-Riemann gradient norm identity, with neither partial
derivative nor its length supplied as an assumption. -/
theorem gradientSq_im (f:ℂ→ℂ) (hf:DifferentiableAt ℂ f 0) :
    gradientSq (fun w=>(f (coord w)).im)=‖deriv f 0‖^2 := by
  have hx:(fun t:ℝ=>(f (coord (t,0))).im)=(fun t:ℝ=>(f (t:ℂ)).im):=by
    funext t;simp [coord]
  have hy:(fun t:ℝ=>(f (coord (0,t))).im)=(fun t:ℝ=>(f ((t:ℂ)*Complex.I)).im):=by
    funext t;simp [coord]
  rw [gradientSq,hx,hy,derivative_x f hf,derivative_y f hf,Complex.sq_norm,Complex.normSq_apply]
  ring
end ImaginaryGradient318
#print axioms ImaginaryGradient318.gradientSq_im
