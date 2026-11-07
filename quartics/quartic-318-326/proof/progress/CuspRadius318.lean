module
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic
public section
noncomputable section
namespace CuspRadius318
set_option maxHeartbeats 0

/-- The shrinking-width estimate is an actual consequence of convexity. -/
theorem gap_lower (A m : ℝ) (hm : 1≤m) :
    (1-Real.exp (-A))/m ≤ 1-Real.exp (-A/m) := by
  have hm0 : 0<m := by linarith
  have hi : 1/m≤1 := (div_le_iff₀ hm0).mpr (by linarith)
  obtain ⟨_, hconv⟩ := convexOn_exp
  have hc := hconv (x:=(-A)) (by trivial) (y:=(0:ℝ)) (by trivial)
    (a:=1/m) (b:=1-1/m) (by positivity) (by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
  have hid : (1/m)*(-A) = -A/m := by ring
  rw [hid] at hc
  have he : (1-Real.exp (-A))/m=1/m-(1/m)*Real.exp (-A) := by ring
  rw [he]
  linarith

theorem fixed_radius_constant :
    Real.exp (-21) ≤ Real.exp (-6*Real.pi)*(1-Real.exp (-14*Real.pi))/2 := by
  have hpi := Real.pi_lt_d2
  have hpi' := Real.pi_gt_three
  have h1 : Real.exp (-19) ≤ Real.exp (-6*Real.pi) := Real.exp_le_exp.mpr (by linarith)
  have hex : (2:ℝ)<Real.exp 1 := Real.exp_one_gt_two
  have hinv : Real.exp (-1) < (1:ℝ)/2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith
  have h2 : Real.exp (-14*Real.pi) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have hgap : (1:ℝ)/2≤1-Real.exp (-14*Real.pi) := by linarith
  have he2 : (4:ℝ)≤Real.exp 2 := by
    have hid : Real.exp (2:ℝ)=Real.exp 1*Real.exp 1 := by rw [←Real.exp_add]; norm_num
    rw [hid]; nlinarith
  have hid : Real.exp (-21)*Real.exp 2=Real.exp (-19) := by rw [←Real.exp_add]; norm_num
  have h3 : 4*Real.exp (-21)≤Real.exp (-19) := by nlinarith [Real.exp_pos (-21)]
  have hp := mul_le_mul h1 hgap (by norm_num : (0:ℝ)≤1/2) (Real.exp_pos _).le
  nlinarith

@[expose] def outer (m:ℝ) : ℝ := Real.exp (-6*Real.pi/m)
@[expose] def inner (m:ℝ) : ℝ := Real.exp (-20*Real.pi/m)
@[expose] def radius (m:ℝ) : ℝ := (outer m-inner m)/2

theorem inner_lt_outer (m:ℝ) (hm:0<m) : inner m<outer m := by
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff_of_pos_right hm).mpr
  nlinarith [Real.pi_pos]

theorem radius_pos (m:ℝ) (hm:0<m) : 0<radius m := by
  unfold radius
  linarith [inner_lt_outer m hm]

/-- The exact radius in the source has the needed uniform level lower bound. -/
theorem radius_level_bound (m N:ℝ) (hm:1≤m) (hN:m≤N) :
    Real.exp (-21)/N≤radius m := by
  have hm0 : 0<m := by linarith
  have hN0 : 0<N := lt_of_lt_of_le hm0 hN
  have hout : Real.exp (-6*Real.pi)≤outer m := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hm0).mpr
    nlinarith [Real.pi_pos]
  have hg : (1-Real.exp (-14*Real.pi))/m ≤ 1-Real.exp (-14*Real.pi/m) := by
    convert gap_lower (14*Real.pi) m hm using 1 <;> congr 2 <;> ring
  have hgap0 : 0≤(1-Real.exp (-14*Real.pi))/m := by
    apply div_nonneg _ hm0.le
    have he : Real.exp (-14*Real.pi)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hid : radius m=outer m*(1-Real.exp (-14*Real.pi/m))/2 := by
    unfold radius outer inner
    have he : Real.exp (-6*Real.pi/m)*Real.exp (-14*Real.pi/m)=Real.exp (-20*Real.pi/m) := by
      rw [←Real.exp_add]; congr 1; ring
    nlinarith
  have hb := mul_le_mul hout hg hgap0 (Real.exp_pos _).le
  have hc := div_le_div_of_nonneg_right fixed_radius_constant hm0.le
  have hr : Real.exp (-21)/m≤radius m := by
    rw [hid]
    have he : (Real.exp (-6*Real.pi)*(1-Real.exp (-14*Real.pi))/2)/m =
      Real.exp (-6*Real.pi)*((1-Real.exp (-14*Real.pi))/m)/2 := by ring
    rw [he] at hc
    linarith
  exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hm0 hN).trans hr

/-- The actual closed centered disc stays strictly inside the cusp chart. -/
theorem centered_disc_inside (m:ℝ) (hm:0<m) (b z:ℂ)
    (hb : ‖b‖ ≤ inner m) (hz:‖z-b‖≤radius m) : ‖z‖<outer m := by
  have htri : ‖z‖≤‖z-b‖+‖b‖ := by simpa using norm_add_le (z-b) b
  have hg := inner_lt_outer m hm
  unfold radius at hz
  linarith

end CuspRadius318
#print axioms CuspRadius318.gap_lower
#print axioms CuspRadius318.fixed_radius_constant
#print axioms CuspRadius318.radius_level_bound
#print axioms CuspRadius318.centered_disc_inside
