module
public import CuspModular318
public import CuspWidthDerivative318
public import CuspHeight318
public section
noncomputable section
namespace ActualCuspEstimates318
open Function NumberField
set_option maxHeartbeats 0

/-- Actual qj coordinate, actual uniformizer, actual rational height: the
regular qj function's standard analytic properties are the explicit producer
inputs. No radius or differential estimate is assumed. -/
theorem coordinate_estimates (G:ℂ→ℂ)
    (hhol:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z)
    (hbound:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128)
    (hzero:G 0=1) (g i m:ℕ) (hg:2≤g) (hi:i≤g^3+1) (hm:1≤m)
    (N:ℝ) (hmN:(m:ℝ)≤N) (tau:UpperHalfPlane)
    (hfund:Real.sqrt 3/2≤tau.im)
    (hvalue:G (Periodic.qParam 1 tau)=
      Periodic.qParam 1 tau*(1728*((2:ℂ)^128+i))) :
    10<tau.im ∧
    Real.exp (-21)/N≤CuspRadius318.radius m ∧
    (∀w:ℂ,‖w-Periodic.qParam m tau‖≤CuspRadius318.radius m →
      ‖w‖<CuspRadius318.outer m) ∧
    -Real.log ‖deriv (fun z:ℂ=>1728*z^m/G (z^m)) (Periodic.qParam m tau)‖
      ≤absLogHeight₁ (1/((2:ℚ)^128+i))+9 ∧
    absLogHeight₁ (1/((2:ℚ)^128+i))≤100+3*Real.log (g+1) := by
  let M : ℝ := 2^128+i
  have hM : 0<M := by dsimp [M]; positivity
  have hqnorm : ‖Periodic.qParam 1 tau‖=Real.exp (-2*Real.pi*tau.im) := by
    rw [Periodic.norm_qParam]
    simp only [div_one,UpperHalfPlane.coe_im]
  have hqsmall : ‖Periodic.qParam 1 tau‖≤(1:ℝ)/100 := by
    rw [hqnorm]
    exact (CuspLocation318.fundamental_q_small tau.im hfund).le
  have hqpos : 0<‖Periodic.qParam 1 tau‖ := by rw [hqnorm]; positivity
  have hvalnorm : ‖G (Periodic.qParam 1 tau)‖=
      ‖Periodic.qParam 1 tau‖*(1728*M) := by
    rw [hvalue,norm_mul]
    have he : (1728:ℂ)*((2:ℂ)^128+i)=((1728*M:ℝ):ℂ) := by dsimp [M]; push_cast; ring
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hJ : 1728*M≤128/Real.exp (-2*Real.pi*tau.im) := by
    have hb:=hbound _ hqsmall
    rw [hvalnorm,hqnorm] at hb
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  have hdeep : 10<tau.im := CuspLocation318.imaginary_part_gt_ten tau.im (1728*M) M hJ le_rfl
    (by dsimp [M]; exact le_add_of_nonneg_right (by positivity))
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  obtain ⟨hr,hdisk⟩ := CuspModular318.actual_cusp_disc m N hmR hmN tau hdeep
  refine ⟨hdeep,hr,hdisk,?_,CuspHeight318.candidate_height g i hg hi⟩
  have hc : Periodic.qParam (m:ℝ) tau≠0 := by
    unfold Periodic.qParam
    exact Complex.exp_ne_zero _
  have hc1 : ‖Periodic.qParam (m:ℝ) tau‖≤1 := by
    exact (Periodic.norm_qParam_lt_one (by linarith) tau.im_pos).le
  have hpow := CuspModular318.qParam_power m hm (tau:ℂ)
  have hsmall : ‖(Periodic.qParam (m:ℝ) tau)^m‖≤Real.exp (-20*Real.pi) := by
    rw [hpow,hqnorm]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hvalue' : G ((Periodic.qParam (m:ℝ) tau)^m)=
      (Periodic.qParam (m:ℝ) tau)^m*(1728*(M:ℂ)) := by
    rw [hpow,hvalue]
    congr 2
    dsimp [M]
    push_cast
    rfl
  have hdiff := CuspWidthDerivative318.actual_width_differential G hhol hbound hzero
    m hm (Periodic.qParam (m:ℝ) tau) hc hc1 hsmall M hM hvalue'
  have hheight : absLogHeight₁ (1/((2:ℚ)^128+i))=Real.log M := by
    have hn : 2^128+i≠(0:ℕ) := by positivity
    have hh:=CuspHeight318.reciprocal_nat_height (2^128+i) hn
    dsimp [M]
    convert hh using 1 <;> norm_num
  rw [hheight]
  exact hdiff

end ActualCuspEstimates318
#print axioms ActualCuspEstimates318.coordinate_estimates
