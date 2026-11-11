module
public import RealQuarticAmbient318
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public section
noncomputable section
namespace RealQuarticOvalCover318
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000

/-- The ordinary positive real square root is analytic away from zero.
This follows from the analytic inverse of squaring, with its actual branch. -/
lemma sqrt_analytic {x : ℝ} (hx : 0<x) : AnalyticAt ℝ Real.sqrt x := by
  let a := Real.sqrt x
  have ha : 0<a := Real.sqrt_pos.mpr hx
  have hsq : a^2=x := Real.sq_sqrt hx.le
  have hf : AnalyticAt ℝ (fun t : ℝ => t^2) a := analyticAt_id.pow 2
  have hd : deriv (fun t : ℝ => t^2) a≠0 := by
    have hd' : HasDerivAt (fun t : ℝ => t^2) (2*a) a := by
      simpa using hasDerivAt_pow 2 a
    rw [hd'.deriv]
    positivity
  have he : (Real.sqrt ∘ (fun t : ℝ => t^2)) =ᶠ[𝓝 a] id := by
    filter_upwards [isOpen_Ioi.mem_nhds ha] with t ht
    exact Real.sqrt_sq ht.le
  have hc : AnalyticAt ℝ (Real.sqrt ∘ (fun t : ℝ => t^2)) a := analyticAt_id.congr he.symm
  have hh := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).mp hc
  simpa only [hsq] using hh

@[expose] def radius (d : ℝ) : ℝ := (Real.sqrt (Real.sqrt d))⁻¹

lemma radius_positive {d : ℝ} (hd : 0<d) : 0<radius d := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hd))

lemma radius_fourth {d : ℝ} (hd : 0<d) : d*(radius d)^4=1 := by
  have h1 := Real.sq_sqrt hd.le
  have h2 := Real.sq_sqrt (Real.sqrt_nonneg d)
  have hne : Real.sqrt (Real.sqrt d)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hd))
  unfold radius
  field_simp [hne]
  nlinarith

@[expose] def u (d t : ℝ) : ℝ := radius d*Real.sin t
@[expose] def v (t : ℝ) : ℝ := Real.cos t*Real.sqrt (1+(Real.sin t)^2)

theorem oval_equation {d : ℝ} (hd : 0<d) (t : ℝ) : (v t)^2=1-d*(u d t)^4 := by
  have hs := Real.sin_sq_add_cos_sq t
  have hr := radius_fourth hd
  have hroot : (Real.sqrt (1+(Real.sin t)^2))^2=1+(Real.sin t)^2 := Real.sq_sqrt (by positivity)
  dsimp [u,v]
  rw [mul_pow,mul_pow,hroot]
  nlinarith [sq_nonneg ((Real.sin t)^2)]

lemma u_analytic (d t : ℝ) : AnalyticAt ℝ (u d) t :=
  analyticAt_const.mul Real.analyticAt_sin

lemma v_analytic (t : ℝ) : AnalyticAt ℝ v t := by
  have hp : 0<1+(Real.sin t)^2 := by positivity
  have hi : AnalyticAt ℝ (fun s : ℝ => 1+(Real.sin s)^2) t :=
    analyticAt_const.add (Real.analyticAt_sin.pow 2)
  exact Real.analyticAt_cos.mul ((sqrt_analytic hp).comp (f:=fun s : ℝ => 1+(Real.sin s)^2) (x:=t) hi)

/-- This covers the entire ordinary real oval, including both signs of v,
the two turning points v=0 and both points with u=0. -/
theorem oval_surjective {d : ℝ} (hd : 0<d) (a b : ℝ) (he : b^2=1-d*a^4) :
    ∃ t : ℝ, u d t=a ∧ v t=b := by
  let r := a/radius d
  have hc : 0<radius d := radius_positive hd
  have hc0 := ne_of_gt hc
  have hr4 : r^4=d*a^4 := by
    dsimp [r]
    have hh := radius_fourth hd
    field_simp [hc0]
    nlinarith
  have hr2 : r^2≤1 := by nlinarith [sq_nonneg b,sq_nonneg (r^2),sq_nonneg r]
  have hrabs : |r|≤1 := (sq_le_one_iff_abs_le_one _).mp hr2
  have hsin : Real.sin (Real.arcsin r)=r := Real.sin_arcsin (abs_le.mp hrabs).1 (abs_le.mp hrabs).2
  have hcos : 0≤Real.cos (Real.arcsin r) := Real.cos_arcsin_nonneg r
  have hroot : (Real.sqrt (1+r^2))^2=1+r^2 := Real.sq_sqrt (by positivity)
  have hsq : (Real.cos (Real.arcsin r)*Real.sqrt (1+r^2))^2=b^2 := by
    have hs := Real.sin_sq_add_cos_sq (Real.arcsin r)
    rw [hsin] at hs
    rw [mul_pow,hroot]
    nlinarith
  have hnon : 0≤Real.cos (Real.arcsin r)*Real.sqrt (1+r^2) :=
    mul_nonneg hcos (Real.sqrt_nonneg _)
  have hau : radius d*r=a := by dsimp [r]; field_simp
  by_cases hb : 0≤b
  · refine ⟨Real.arcsin r,?_,?_⟩
    · simpa only [u,hsin] using hau
    · dsimp [v]
      rw [hsin]
      exact (sq_eq_sq₀ hnon hb).mp hsq
  · refine ⟨Real.pi-Real.arcsin r,?_,?_⟩
    · simpa only [u,Real.sin_pi_sub,hsin] using hau
    · dsimp [v]
      rw [Real.cos_pi_sub,Real.sin_pi_sub,hsin,neg_mul]
      have hb' : 0≤ -b := by linarith
      have heq : Real.cos (Real.arcsin r)*Real.sqrt (1+r^2)= -b :=
        (sq_eq_sq₀ hnon hb').mp (by simpa only [neg_sq] using hsq)
      linarith

end RealQuarticOvalCover318
