module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public section
open Complex MeasureTheory Set
open scoped Real
namespace CircleEnergy318
set_option maxHeartbeats 0
noncomputable section

/-- The elementary interval Cauchy–Schwarz estimate, proved by integrating
 the nonnegative variance. No coefficient bound is supplied as a premise. -/
theorem integral_sq_le (g:ℝ→ℝ) (hg:Continuous g) (T:ℝ) (hT:0<T) :
    (∫ θ in (0:ℝ)..T,g θ)^2 ≤ T*(∫ θ in (0:ℝ)..T,(g θ)^2) := by
  let A:ℝ:=∫ θ in (0:ℝ)..T,g θ
  let m:ℝ:=A/T
  have hm:T*m=A := by dsimp [m]; field_simp
  have hi:0≤∫ θ in (0:ℝ)..T,(g θ-m)^2 :=
    intervalIntegral.integral_nonneg hT.le (fun θ _=>sq_nonneg _)
  have he: (∫ θ in (0:ℝ)..T,(g θ-m)^2)=
      (∫ θ in (0:ℝ)..T,(g θ)^2)-2*m*A+T*m^2 := by
    calc
      _ = ∫ θ in (0:ℝ)..T,((g θ)^2-(2*m)*g θ)+m^2 := by
        apply intervalIntegral.integral_congr
        intro θ _
        ring
      _ = _ := by
        have hsq:IntervalIntegrable (fun θ=>g θ^2) volume 0 T := (hg.pow 2).intervalIntegrable 0 T
        have hlin:IntervalIntegrable (fun θ=>(2*m)*g θ) volume 0 T :=
          (continuous_const.mul hg).intervalIntegrable 0 T
        have hconst:IntervalIntegrable (fun _:ℝ=>m^2) volume 0 T := continuous_const.intervalIntegrable 0 T
        rw [intervalIntegral.integral_add (hsq.sub hlin) hconst,
          intervalIntegral.integral_sub hsq hlin,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
        simp only [sub_zero,smul_eq_mul]
        rfl
  rw [he] at hi
  have hp:=mul_nonneg hT.le hi
  change A^2≤T*(∫ θ in (0:ℝ)..T,(g θ)^2)
  nlinarith only [hp,hm]

@[expose] def coefficient (f:ℂ→ℂ) (c:ℂ) (j:ℕ) : ℂ := iteratedDeriv j f c/(j.factorial:ℂ)

/-- Cauchy's actual coefficient formula gives the L1 boundary estimate. -/
theorem coefficient_l1 (f:ℂ→ℂ) (c:ℂ) (r:ℝ) (hr:0<r)
    (hf:DifferentiableOn ℂ f (Metric.closedBall c r)) (j:ℕ) :
    (2*Real.pi)*‖coefficient f c j‖*r^j ≤
      ∫ θ in (0:ℝ)..2*Real.pi,‖f (circleMap c r θ)‖ := by
  let g:ℝ→ℂ:=fun θ=>deriv (circleMap c r) θ*((1/(circleMap c r θ-c)^(j+1))*f (circleMap c r θ))
  have hc:=hf.circleIntegral_one_div_sub_center_pow_smul hr j
  have hc': (∫ θ in (0:ℝ)..2*Real.pi,g θ)=(2*Real.pi*I:ℂ)*coefficient f c j := by
    change (∫ θ in (0:ℝ)..2*Real.pi,g θ)=(2*Real.pi*I/(j.factorial:ℂ))*iteratedDeriv j f c at hc
    rw [hc]
    dsimp [coefficient]
    ring
  have hn (θ:ℝ):r^j*‖g θ‖=‖f (circleMap c r θ)‖ := by
    have hz:‖circleMap c r θ-c‖=r := by
      simpa only [Metric.mem_sphere,dist_eq_norm] using circleMap_mem_sphere c hr.le θ
    dsimp [g]
    rw [norm_mul,norm_mul,norm_div,norm_one,norm_pow,hz,deriv_circleMap,
      norm_mul,norm_circleMap_zero,norm_I,mul_one,abs_of_pos hr]
    rw [pow_succ]
    field_simp
  have hbound:‖∫ θ in (0:ℝ)..2*Real.pi,g θ‖≤∫ θ in (0:ℝ)..2*Real.pi,‖g θ‖ :=
    intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
  have hp:=mul_le_mul_of_nonneg_left hbound (pow_nonneg hr.le j)
  rw [hc',norm_mul] at hp
  have hnc:‖(2*Real.pi*I:ℂ)‖=2*Real.pi := by simp
  rw [hnc,←intervalIntegral.integral_const_mul] at hp
  have he:(∫ θ in (0:ℝ)..2*Real.pi,r^j*‖g θ‖)=
      ∫ θ in (0:ℝ)..2*Real.pi,‖f (circleMap c r θ)‖ := by
    apply intervalIntegral.integral_congr
    intro θ _
    exact hn θ
  rw [he] at hp
  nlinarith only [hp]

/-- Actual Taylor coefficient versus normalized boundary energy.
All analytic input is holomorphicity on the closed disc. -/
theorem coefficient_energy (f:ℂ→ℂ) (c:ℂ) (r:ℝ) (hr:0<r)
    (hf:DifferentiableOn ℂ f (Metric.closedBall c r)) (j:ℕ) :
    ‖coefficient f c j‖^2*r^(2*j) ≤
      (2*Real.pi)⁻¹*(∫ θ in (0:ℝ)..2*Real.pi,‖f (circleMap c r θ)‖^2) := by
  have hg:Continuous (fun θ:ℝ=>‖f (circleMap c r θ)‖) :=
    (hf.continuousOn.comp_continuous (continuous_circleMap c r)
      (fun θ=>circleMap_mem_closedBall c hr.le θ)).norm
  have hcs:=integral_sq_le _ hg (2*Real.pi) Real.two_pi_pos
  have hL:=coefficient_l1 f c r hr hf j
  have hA:0≤(2*Real.pi)*‖coefficient f c j‖*r^j := by positivity
  have hI:0≤∫ θ in (0:ℝ)..2*Real.pi,‖f (circleMap c r θ)‖ :=
    intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun θ _=>norm_nonneg _)
  have hsq:=sq_le_sq₀ hA hI |>.mpr hL
  have hpow:r^(2*j)=(r^j)^2 := by rw [Nat.mul_comm,pow_mul]
  rw [hpow]
  apply (le_inv_mul_iff₀ Real.two_pi_pos).mpr
  nlinarith only [hcs,hsq,Real.two_pi_pos]

/-- Shift the actual periodic boundary energy to the symmetric angular
interval used by the polar-coordinate integration theorem. -/
theorem circle_energy_interval (f:ℂ→ℂ) (c:ℂ) (r:ℝ) :
    (∫ θ in (0:ℝ)..2*Real.pi,‖f (circleMap c r θ)‖^2)=
      ∫ θ in (-Real.pi)..Real.pi,‖f (circleMap c r θ)‖^2 := by
  have hp:Function.Periodic (fun θ=>‖f (circleMap c r θ)‖^2) (2*Real.pi) :=
    (periodic_circleMap c r).comp (fun z=>‖f z‖^2)
  have he:=hp.intervalIntegral_add_eq 0 (-Real.pi)
  simpa only [zero_add,show -Real.pi+2*Real.pi=Real.pi by ring] using he

/-- The actual factorial-normalized Taylor coefficient and the exact
symmetric angular energy, for any circle strictly inside a holomorphic disc. -/
theorem coefficient_energy_interior (f:ℂ→ℂ) (c:ℂ) (rho r:ℝ)
    (hf:DifferentiableOn ℂ f (Metric.ball c rho)) (hr:0<r) (hrr:r<rho) (j:ℕ) :
    ‖iteratedDeriv j f c/(j.factorial:ℂ)‖^2*r^(2*j) ≤
      (2*Real.pi)⁻¹*(∫ θ in (-Real.pi)..Real.pi,
        ‖f (c+(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖^2) := by
  have he:=coefficient_energy f c r hr (hf.mono (Metric.closedBall_subset_ball hrr)) j
  rw [circle_energy_interval] at he
  simpa only [coefficient,circleMap] using he

end
end CircleEnergy318
#print axioms CircleEnergy318.coefficient_energy

#print axioms CircleEnergy318.coefficient_energy_interior
