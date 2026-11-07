module
public import WronskianFinite318
public import Mathlib.Analysis.Real.Pi.Bounds
public section
namespace WronskianCoefficient318
open WronskianFinite318
noncomputable section
set_option maxHeartbeats 0

 theorem radius_inverse_bound (N rho:ℝ) (hN:1≤N)
    (hr:Real.exp (-21)/N≤rho) : 0<rho ∧ rho⁻¹≤Real.exp 21*N ∧ 1≤Real.exp 21*N := by
  have hNp:0<N:=by linarith
  have hrp:0<rho:=(div_pos (Real.exp_pos _) hNp).trans_le hr
  have he:1≤Real.exp (21:ℝ) := (Real.one_le_exp_iff).mpr (by norm_num)
  have hA:1≤Real.exp (21:ℝ)*N:=by nlinarith
  have hh:=mul_le_mul_of_nonneg_left hr (show 0≤Real.exp 21*N by positivity)
  have hc:(Real.exp 21*N)*(Real.exp (-21)/N)=1 := by
    field_simp
    rw [←Real.exp_add]
    norm_num
  rw [hc] at hh
  refine ⟨hrp,?_,hA⟩
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hrp).mpr hh

 theorem coefficient_bound (g:ℕ) (hg:1≤g) (N rho:ℝ) (hN:1≤N)
    (hr:Real.exp (-21)/N≤rho) (j:Fin g) :
    Real.sqrt ((j.val+1:ℝ)/Real.pi)*(rho⁻¹)^(j.val+1)≤(g:ℝ)*(Real.exp 21*N)^g := by
  obtain ⟨hrp,hri,hA⟩:=radius_inverse_bound N rho hN hr
  have hgR:(1:ℝ)≤g:=by exact_mod_cast hg
  have hj:(j.val+1:ℝ)≤g:=by exact_mod_cast (show j.val+1≤g by omega)
  have hs:Real.sqrt ((j.val+1:ℝ)/Real.pi)≤(g:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three, sq_nonneg (g:ℝ)]
  have hp:(rho⁻¹)^(j.val+1)≤(Real.exp 21*N)^g :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hrp.le) hri _).trans
      (pow_le_pow_right₀ hA (by omega))
  exact mul_le_mul hs hp (pow_nonneg (inv_nonneg.mpr hrp.le) _) (by positivity)

/-- The actual factorial-normalized Wronskian bound. The local analytic
coefficient estimate remains the displayed input until its disk-energy proof
is formalized; it is not inferred from an unspecified L2 normalization. -/
theorem actual_wronskian_bound (g:ℕ) (hg:1≤g) (N rho:ℝ) (hN:1≤N)
    (hr:Real.exp (-21)/N≤rho) (f:Fin g→ℂ→ℂ) (b:ℂ)
    (hc:∀i j:Fin g,‖iteratedDeriv j.val (f i) b/(j.val.factorial:ℂ)‖≤
      Real.sqrt ((j.val+1:ℝ)/Real.pi)*(rho⁻¹)^(j.val+1)) :
    Real.log ‖wronskian g f b‖≤100*(g:ℝ)^2*Real.log (2*g*N) := by
  apply logarithmic_det_bound g hg N hN
  intro i j
  exact (hc i j).trans (coefficient_bound g hg N rho hN hr j)

end
end WronskianCoefficient318
#print axioms WronskianCoefficient318.actual_wronskian_bound
