module
public import ActualInfinityEquation318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace AnalyticScalingGerm318
open PeriodEisenstein318 LatticeInvariants318 InfinityAnalyticChart318
open InfinityBranchUniqueness318 ActualInfinityEquation318
set_option maxHeartbeats 0

/-- A genuine holomorphic lift near the actual infinity point of an exact
short-model scaling. This alone does not assert the lift is linear. -/
theorem exists_scaling_germ (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve sigma).a₄=
      (u:ℂ)^4*(ModularWeierstrass318.curve tau).a₄)
    (h6 : (ModularWeierstrass318.curve sigma).a₆=
      (u:ℂ)^6*(ModularWeierstrass318.curve tau).a₆) :
    ∃ w : ℂ → ℂ, AnalyticAt ℂ w 0 ∧ w 0=0 ∧ HasDerivAt w (u:ℂ)⁻¹ 0 ∧
      (fun z => t sigma (w z)) =ᶠ[𝓝 0] (fun z => (u:ℂ)⁻¹*t tau z) ∧
      (fun z => v sigma (w z)) =ᶠ[𝓝 0] (fun z => ((u:ℂ)⁻¹)^3*v tau z) := by
  obtain ⟨g,hg,hg0,hl,hr,hvg⟩ := exists_infinity_inverse sigma
  let a : ℂ → ℂ := fun z => (u:ℂ)⁻¹*t tau z
  have ha : AnalyticAt ℂ a 0 := analyticAt_const.mul (t_analytic tau)
  have ha0 : a 0=0 := by simp [a,t_zero]
  have hat : Tendsto a (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt,ha0] using ha.continuousAt
  let w : ℂ → ℂ := fun z => g (a z)
  have hw : AnalyticAt ℂ w 0 := by
    have hg' : AnalyticAt ℂ g (a 0) := by rw [ha0]; exact hg
    exact hg'.comp (f := a) ha
  have hw0 : w 0=0 := by simp [w,ha0,hg0]
  have hwt : Tendsto w (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt,hw0] using hw.continuousAt
  have ht : (fun z => t sigma (w z)) =ᶠ[𝓝 0] a := by
    simpa only [w,Function.comp_def,id_eq] using hr.comp_tendsto hat
  have hvw : ContinuousAt (fun z => v sigma (w z)) 0 := by
    have hv' : ContinuousAt (v sigma) (w 0) := by rw [hw0]; exact (v_analytic sigma).continuousAt
    exact hv'.comp hw.continuousAt
  have hvs : ContinuousAt (fun z => ((u:ℂ)⁻¹)^3*v tau z) 0 := by
    exact (v_analytic tau).continuousAt.const_mul _
  have hev : ∀ᶠ z in 𝓝 (0:ℂ), equation (ModularWeierstrass318.curve sigma).a₄
      (ModularWeierstrass318.curve sigma).a₆ (a z) (v sigma (w z))=0 := by
    filter_upwards [hwt.eventually (equation_germ sigma),ht] with z hz htz
    rw [← htz]
    exact hz
  have hes : ∀ᶠ z in 𝓝 (0:ℂ), equation (ModularWeierstrass318.curve sigma).a₄
      (ModularWeierstrass318.curve sigma).a₆ (a z) (((u:ℂ)⁻¹)^3*v tau z)=0 := by
    filter_upwards [equation_germ tau] with z hz
    dsimp only [a]
    rw [h4,h6,equation_scale,hz,mul_zero]
  have hv := unique_germ _ _ a (fun z => v sigma (w z))
    (fun z => ((u:ℂ)⁻¹)^3*v tau z) ha.continuousAt hvw hvs ha0
    (by rw [hw0,v_zero]) (by simp [v_zero]) hev hes
  have hD : HasDerivAt w (u:ℂ)⁻¹ 0 := by
    have hts : HasDerivAt (t sigma) (2*(Real.pi:ℂ)) (w 0) := by
      rw [hw0]
      exact t_hasDerivAt sigma
    have hleft := hts.comp (0:ℂ) hw.differentiableAt.hasDerivAt
    have hright := (t_hasDerivAt tau).const_mul ((u:ℂ)⁻¹)
    have he := hleft.unique (hright.congr_of_eventuallyEq ht)
    have hk : (2*(Real.pi:ℂ))≠0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hd : deriv w 0=(u:ℂ)⁻¹ := by
      apply mul_left_cancel₀ hk
      simpa only [mul_comm] using he
    simpa only [hd] using hw.differentiableAt.hasDerivAt
  exact ⟨w,hw,hw0,hD,ht,hv⟩

end AnalyticScalingGerm318
