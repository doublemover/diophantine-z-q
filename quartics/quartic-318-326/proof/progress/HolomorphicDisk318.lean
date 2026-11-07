module
public import DiskEnergy318
public import CircleEnergy318
public section
noncomputable section
open Set MeasureTheory Metric
open scoped Real
namespace HolomorphicDisk318
set_option maxHeartbeats 0

/-- Sharp disk-energy lower bound for an actual Taylor coefficient. Energy
is the ordinary area integral in centered local coordinates. -/
theorem coefficient_energy (f:ℂ→ℂ) (c:ℂ) (rho:ℝ) (hrho:0<rho)
    (hf:DifferentiableOn ℂ f (ball c rho))
    (hfi:IntegrableOn (fun z:ℂ=>‖f (c+z)‖^2) (ball 0 rho)) (j:ℕ) :
    Real.pi*‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2*rho^(2*j+2)/(j+1) ≤
      ∫z in ball (0:ℂ) rho,‖f (c+z)‖^2 := by
  have hR (R:ℝ) (hr:R∈Ioo 0 rho) :
      Real.pi*‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2*R^(2*j+2)/(j+1) ≤
        ∫z in ball (0:ℂ) rho,‖f (c+z)‖^2 := by
    have hc:ContinuousOn (fun z:ℂ=>‖f (c+z)‖^2) (closedBall 0 R) := by
      have hfc:ContinuousOn (fun z:ℂ=>f (c+z)) (closedBall 0 R) := by
        apply hf.continuousOn.comp (continuous_const.add continuous_id).continuousOn
        intro z hz
        simp only [mem_ball,dist_eq_norm,Pi.add_apply,id_eq,add_sub_cancel_left]
        have hz':‖z‖≤R:=by simpa only [mem_closedBall,dist_zero_right] using hz
        exact hz'.trans_lt hr.2
      exact hfc.norm.pow 2
    have hl:=DiskEnergy318.disk_energy_lower (fun z:ℂ=>‖f (c+z)‖^2) R
      (‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2) j hr.1 hc (by
        intro r hrr
        have he:=CircleEnergy318.coefficient_energy_interior f c rho r hf hrr.1 (hrr.2.trans hr.2) j
        simpa only [Complex.polarCoord_symm_apply,Complex.exp_ofReal_mul_I] using he)
    exact hl.trans (setIntegral_mono_set hfi (Filter.Eventually.of_forall (fun z=>sq_nonneg _))
      (Filter.Eventually.of_forall (fun z hz=>ball_subset_ball hr.2.le hz)))
  apply ContinuousWithinAt.closure_le (s:=Ioo 0 rho)
    (g:=fun _ : ℝ => ∫z in ball (0:ℂ) rho,‖f (c+z)‖^2)
    (show rho∈closure (Ioo 0 rho) by rw [closure_Ioo hrho.ne]; exact ⟨hrho.le,le_rfl⟩)
  · exact (by fun_prop : Continuous (fun R:ℝ=>
      Real.pi*‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2*R^(2*j+2)/(j+1))).continuousWithinAt
  · exact continuous_const.continuousWithinAt
  · exact hR

/-- The actual normalized holomorphic-disc coefficient estimate, not a
supplied coefficient bound. The hypotheses are holomorphicity and finite
area energy at most one. -/
theorem coefficient_bound (f:ℂ→ℂ) (c:ℂ) (rho:ℝ) (hrho:0<rho)
    (hf:DifferentiableOn ℂ f (ball c rho))
    (hfi:IntegrableOn (fun z:ℂ=>‖f (c+z)‖^2) (ball 0 rho))
    (hL2:(∫z in ball (0:ℂ) rho,‖f (c+z)‖^2)≤1) (j:ℕ) :
    ‖iteratedDeriv j f c/(j.factorial:ℂ)‖ ≤
      Real.sqrt ((j+1:ℝ)/Real.pi)*(rho⁻¹)^(j+1) := by
  have he:Real.pi*‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2*rho^(2*j+2)/(j+1)≤1 :=
    (coefficient_energy f c rho hrho hf hfi j).trans hL2
  have hj:0<(j:ℝ)+1:=by positivity
  have hs:=Real.sq_sqrt (show 0≤(j+1:ℝ)/Real.pi by positivity)
  have hp:rho^(2*j+2)=(rho^(j+1))^2 := by rw [←pow_mul]; congr 1; omega
  have hrn:rho^(j+1)≠0:=pow_ne_zero _ hrho.ne'
  have hh:‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2≤
      (Real.sqrt ((j+1:ℝ)/Real.pi)*(rho⁻¹)^(j+1))^2 := by
    rw [mul_pow,hs,inv_pow,inv_pow,←div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_ne_zero hrn)).mpr
    apply (le_div_iff₀ Real.pi_pos).mpr
    have he':Real.pi*‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2*rho^(2*j+2)≤(j:ℝ)+1 :=
      (div_le_one hj).mp he
    rw [hp] at he'
    nlinarith only [he']
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hh

end HolomorphicDisk318
#print axioms HolomorphicDisk318.coefficient_energy
#print axioms HolomorphicDisk318.coefficient_bound
