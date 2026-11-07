module
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic
public section
noncomputable section
open Set MeasureTheory Metric
open scoped Real
namespace DiskEnergy318
set_option maxHeartbeats 0

 theorem polar_continuous : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
  have h : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
      fun p => p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  rw [h]
  fun_prop

 theorem rectangle_integrable (F:ℂ→ℝ) (R:ℝ)
    (hf:ContinuousOn F (closedBall 0 R)) :
    IntegrableOn (fun p:ℝ×ℝ => p.1 * F (Complex.polarCoord.symm p))
      (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hc:ContinuousOn (fun p:ℝ×ℝ => p.1 * F (Complex.polarCoord.symm p))
      (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) := by
    apply continuous_fst.continuousOn.mul
    apply hf.comp polar_continuous.continuousOn
    intro p hp
    simp only [mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
    rw [abs_of_nonneg hp.1.1]
    exact hp.1.2
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (by intro p hp; exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩)

/-- The ordinary two-dimensional Lebesgue integral on the disc equals its
polar-coordinate radial/angular integral, including the radial Jacobian. -/
 theorem disk_integral_polar (F:ℂ→ℝ) (R:ℝ) (hR:0≤R)
    (hf:ContinuousOn F (closedBall 0 R)) :
    (∫z in ball (0:ℂ) R, F z) =
      ∫r in 0..R, r * ∫θ in (-Real.pi)..Real.pi,
        F (Complex.polarCoord.symm (r,θ)) := by
  let S := Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  have hS : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub:S⊆polarCoord.target := by
    intro p hp; exact ⟨hp.1.1,hp.2⟩
  have heq:(∫p in polarCoord.target,
      p.1 • (ball (0:ℂ) R).indicator F (Complex.polarCoord.symm p)) =
      ∫p in S,p.1*F (Complex.polarCoord.symm p) := by
    calc
      _ = ∫p in polarCoord.target,
        S.indicator (fun p:ℝ×ℝ=>p.1*F (Complex.polarCoord.symm p)) p := by
          apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          have hn:‖Complex.polarCoord.symm p‖=p.1 := by
            rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1]
          by_cases hr:p.1<R
          · have hb:Complex.polarCoord.symm p∈ball (0:ℂ) R := by
              simpa only [mem_ball,dist_zero_right,hn] using hr
            have hs:p∈S:=⟨⟨hp.1,hr⟩,hp.2⟩
            simp only [indicator_of_mem hb,indicator_of_mem hs,smul_eq_mul]
          · have hb:Complex.polarCoord.symm p∉ball (0:ℂ) R := by
              simpa only [mem_ball,dist_zero_right,hn] using hr
            have hs:p∉S:=by intro h; exact hr h.1.2
            simp only [indicator_of_notMem hb,indicator_of_notMem hs,smul_zero]
      _ = ∫p in polarCoord.target∩S,p.1*F (Complex.polarCoord.symm p) :=
        setIntegral_indicator hS
      _ = _ := by rw [inter_eq_right.mpr hsub]
  have hp:=Complex.integral_comp_polarCoord_symm ((ball (0:ℂ) R).indicator F)
  rw [integral_indicator measurableSet_ball,heq] at hp
  rw [←hp]
  have hi:=rectangle_integrable F R hf
  change Integrable _ ((volume.prod volume).restrict
    (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi)) at hi
  rw [←Measure.prod_restrict] at hi
  change (∫p, p.1*F (Complex.polarCoord.symm p)
    ∂(volume.prod volume).restrict (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi)) = _
  rw [←Measure.prod_restrict,integral_prod _ hi]
  simp_rw [integral_const_mul]
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hR]
  congr 1
  ext r
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]

/-- Integrating the actual angular energy lower bound gives the sharp
radial coefficient factor π R^(2j+2)/(j+1). -/
theorem disk_energy_lower (F:ℂ→ℝ) (R A:ℝ) (j:ℕ) (hR:0<R)
    (hf:ContinuousOn F (closedBall 0 R))
    (hc:∀r∈Ioo 0 R, A*r^(2*j)≤(2*Real.pi)⁻¹ *
      ∫θ in (-Real.pi)..Real.pi,F (Complex.polarCoord.symm (r,θ))) :
    Real.pi*A*R^(2*j+2)/(j+1)≤∫z in ball (0:ℂ) R,F z := by
  have hi:=rectangle_integrable F R hf
  change Integrable _ ((volume.prod volume).restrict
    (Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi)) at hi
  rw [←Measure.prod_restrict] at hi
  have hlow:IntegrableOn (fun r:ℝ=>(2*Real.pi)*A*r^(2*j+1)) (Ioo 0 R) :=
    ((by fun_prop : Continuous (fun r:ℝ=>(2*Real.pi)*A*r^(2*j+1))).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hm:=setIntegral_mono_on hlow hi.integral_prod_left measurableSet_Ioo (fun r hr=> by
    have hh:=hc r hr
    have hp:=mul_le_mul_of_nonneg_left hh (mul_nonneg Real.two_pi_pos.le hr.1.le)
    have hconst:(2*Real.pi)*r*((2*Real.pi)⁻¹ *
        ∫θ in (-Real.pi)..Real.pi,F (Complex.polarCoord.symm (r,θ))) =
        ∫θ in Ioo (-Real.pi) Real.pi,r*F (Complex.polarCoord.symm (r,θ)) := by
      rw [integral_const_mul,←integral_Ioc_eq_integral_Ioo,
        ←intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      field_simp
    rw [hconst] at hp
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hp)
  have he:(∫r in Ioo 0 R,(2*Real.pi)*A*r^(2*j+1)) =
      Real.pi*A*R^(2*j+2)/(j+1) := by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hR.le,
      intervalIntegral.integral_const_mul,integral_pow]
    simp only [show 2*j+1+1=2*j+2 by omega,zero_pow (by omega : 2*j+2≠0),sub_zero]
    push_cast
    field_simp
    ring
  rw [he] at hm
  have hp:=disk_integral_polar F R hR.le hf
  rw [hp]
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hR.le] at hm
  simp_rw [integral_const_mul] at hm
  have ha : (∫r in 0..R, r * ∫θ in Ioo (-Real.pi) Real.pi,
      F (Complex.polarCoord.symm (r,θ))) =
      ∫r in 0..R,r * ∫θ in (-Real.pi)..Real.pi,F (Complex.polarCoord.symm (r,θ)) := by
    congr 1
    ext r
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [ha] at hm
  exact hm

end DiskEnergy318
#print axioms DiskEnergy318.disk_integral_polar

#print axioms DiskEnergy318.disk_energy_lower
