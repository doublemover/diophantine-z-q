module
public import RealOvalNormalization318
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Order.IntermediateValue
public section
noncomputable section

/-! An actual positive periodic clock reparametrizes the full quartic oval
by its invariant polynomial differential equation. Additivity is not assumed. -/
namespace OvalInvariantClock318
open Set Filter RealQuarticGroup318
open scoped Topology
set_option maxHeartbeats 2000000

@[expose] def rho (t : ℝ) : ℝ := Real.sqrt (1+(Real.sin t)^2)
@[expose] def speed (t : ℝ) : ℝ := (rho t)⁻¹

lemma rho_pos (t : ℝ) : 0<rho t := Real.sqrt_pos.mpr (by positivity)
lemma rho_square (t : ℝ) : (rho t)^2=1+(Real.sin t)^2 := Real.sq_sqrt (by positivity)
lemma speed_pos (t : ℝ) : 0<speed t := inv_pos.mpr (rho_pos t)

lemma speed_continuous : Continuous speed := by
  unfold speed
  apply Continuous.inv₀
  · unfold rho
    fun_prop
  · exact fun t => (rho_pos t).ne'

lemma speed_periodic : Function.Periodic speed (2*Real.pi) := by
  intro t
  simp [speed,rho,Real.sin_add_two_pi]

@[expose] def clock (t : ℝ) : ℝ := ∫ s in 0..t, speed s
@[expose] def period : ℝ := clock (2*Real.pi)

lemma clock_zero : clock 0=0 := by simp [clock]

lemma clock_hasStrictDeriv (t : ℝ) : HasStrictDerivAt clock (speed t) t :=
  speed_continuous.integral_hasStrictDerivAt 0 t

lemma clock_continuous : Continuous clock :=
  continuous_iff_continuousAt.mpr fun t => (clock_hasStrictDeriv t).continuousAt

lemma clock_strictMono : StrictMono clock :=
  strictMono_of_deriv_pos fun t => by rw [(clock_hasStrictDeriv t).hasDerivAt.deriv]; exact speed_pos t

lemma period_pos : 0<period := by
  have h := clock_strictMono (show (0:ℝ)<2*Real.pi by positivity)
  simpa only [clock_zero,period] using h

lemma clock_shift (t : ℝ) : clock (t+2*Real.pi)=clock t+period := by
  simpa only [clock,period,_root_.zero_add] using speed_periodic.intervalIntegral_add_eq_add 0 t
    (fun a b => speed_continuous.intervalIntegrable a b)

lemma clock_surjective : Function.Surjective clock :=
  clock_continuous.surjective
    (speed_periodic.tendsto_atTop_intervalIntegral_of_pos period_pos (by positivity))
    (speed_periodic.tendsto_atBot_intervalIntegral_of_pos period_pos (by positivity))

@[expose] def clockOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective clock clock_strictMono clock_surjective

@[expose] def angle (s : ℝ) : ℝ := clockOrderIso.symm s

lemma angle_clock (t : ℝ) : angle (clock t)=t := clockOrderIso.symm_apply_apply t
lemma clock_angle (s : ℝ) : clock (angle s)=s := clockOrderIso.apply_symm_apply s

lemma angle_zero : angle 0=0 := by simpa only [clock_zero] using angle_clock 0

lemma angle_shift (s : ℝ) : angle (s+period)=angle s+2*Real.pi := by
  apply clock_strictMono.injective
  rw [clock_angle,clock_shift,clock_angle]

/-- The inverse clock has exactly the reciprocal speed required for the
quartic invariant vector field. -/
lemma angle_hasDeriv (s : ℝ) : HasDerivAt angle (rho (angle s)) s := by
  have hi := (clock_hasStrictDeriv (angle s)).to_local_left_inverse
    (speed_pos (angle s)).ne' (Filter.Eventually.of_forall angle_clock)
  simpa only [clock_angle,speed,inv_inv] using hi.hasDerivAt

lemma rho_hasDeriv (t : ℝ) :
    HasDerivAt rho (Real.sin t*Real.cos t/rho t) t := by
  have h := (((Real.hasDerivAt_sin t).pow 2).const_add 1).sqrt
    (by positivity : (1+(Real.sin t)^2:ℝ)≠0)
  convert h using 1 <;> dsimp [rho] <;> field_simp [(rho_pos t).ne'] <;> ring

lemma v_hasDeriv (t : ℝ) :
    HasDerivAt RealQuarticOvalCover318.v (-2*(Real.sin t)^3*speed t) t := by
  have h := (Real.hasDerivAt_cos t).mul (rho_hasDeriv t)
  have he : -Real.sin t*rho t+Real.cos t*(Real.sin t*Real.cos t/rho t)=
      -2*(Real.sin t)^3*speed t := by
    unfold speed
    field_simp [(rho_pos t).ne']
    linear_combination -(Real.sin t)*rho_square t+
      (Real.sin t)*(Real.sin_sq_add_cos_sq t)
  simpa only [he,RealQuarticOvalCover318.v,rho] using h

@[expose] def flow (s : ℝ) : Oval 1 :=
  ⟨(Real.sin (angle s),RealQuarticOvalCover318.v (angle s)),by
    simpa [RealQuarticOvalCover318.u,RealQuarticOvalCover318.radius] using
      RealQuarticOvalCover318.oval_equation (d:=1) (by norm_num) (angle s)⟩

lemma flow_zero : (flow 0).val=(0,1) := by
  simp [flow,angle_zero,RealQuarticOvalCover318.v]

lemma flow_periodic : Function.Periodic flow period := by
  intro s
  apply Subtype.ext
  simp [flow,angle_shift,RealQuarticOvalCover318.v,Real.sin_add_two_pi,Real.cos_add_two_pi]

lemma flow_surjective : Function.Surjective flow := by
  intro p
  obtain ⟨t,hu,hv⟩ := RealQuarticOvalCover318.oval_surjective (d:=1) (by norm_num)
    p.val.1 p.val.2 p.property
  refine ⟨clock t,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · simpa [flow,angle_clock,RealQuarticOvalCover318.u,RealQuarticOvalCover318.radius] using hu
  · simpa only [flow,angle_clock] using hv

lemma flow_u_hasDeriv (s : ℝ) : HasDerivAt (fun t => (flow t).val.1) (flow s).val.2 s := by
  simpa only [flow,RealQuarticOvalCover318.v,rho] using
    (Real.hasDerivAt_sin (angle s)).comp s (angle_hasDeriv s)

lemma flow_v_hasDeriv (s : ℝ) :
    HasDerivAt (fun t => (flow t).val.2) (-2*(flow s).val.1^3) s := by
  have h := (v_hasDeriv (angle s)).comp s (angle_hasDeriv s)
  have he : (-2*(Real.sin (angle s))^3*speed (angle s))*rho (angle s)=
      -2*(Real.sin (angle s))^3 := by
    unfold speed
    field_simp [(rho_pos (angle s)).ne']
  simpa only [he,flow] using h

/-- This actual globally defined periodic surjection solves the normalized
autonomous system. The additive-circle identification still requires proving
translation preserves this system and invoking uniqueness. -/
theorem flow_hasDeriv (s : ℝ) :
    HasDerivAt (fun t => (flow t).val) ((flow s).val.2,-2*(flow s).val.1^3) s :=
  (flow_u_hasDeriv s).prodMk (flow_v_hasDeriv s)

lemma flow_continuous : Continuous flow := by
  apply continuous_induced_rng.mpr
  exact continuous_iff_continuousAt.mpr fun s => (flow_hasDeriv s).continuousAt

end OvalInvariantClock318
