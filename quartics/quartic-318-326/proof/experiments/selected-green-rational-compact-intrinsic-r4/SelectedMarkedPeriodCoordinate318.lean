module
public import ThirdPeriodSummands318
public import CanonicalXModularity318
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public section
noncomputable section
open Filter Set Function
open scoped Topology MatrixGroups
open UniformPeriodBounds318 PeriodEisenstein318 OpenJComplexEvaluation318
open CanonicalXModularity318 ModularCurveChange318

namespace SelectedMarkedPeriodCoordinate318

private def term (a : ℂ) (v : Fin 2 → ℤ) (z : ℂ) : ℂ :=
  if v=0 then 0 else 1/(a-period v z)^2-1/(period v z)^2

private theorem term_analyticAt (a : ℂ) (tau : UpperHalfPlane)
    (ha : a ∉ (periods tau).lattice) (v : Fin 2 → ℤ) :
    AnalyticAt ℂ (term a v) (tau : ℂ) := by
  have hn : a ≠ period v (tau : ℂ) := by
    intro he
    apply ha
    rw [he]
    exact (latticeMap tau v).property
  unfold term
  by_cases hv : v=0
  · simp only [hv,ite_true]
    exact analyticAt_const
  · have hp : AnalyticAt ℂ (period v) (tau:ℂ) := by unfold period; fun_prop
    simp only [hv,ite_false]
    exact (analyticAt_const.div ((analyticAt_const.sub hp).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr hn))).sub
      (analyticAt_const.div (hp.pow 2) (pow_ne_zero 2 (period_ne_zero tau hv)))

private theorem term_bound (a : ℂ) (ha : ‖a‖ < 1) (tau : UpperHalfPlane)
    (v : Fin 2 → ℤ) (z : ℂ) (hz : ‖z-(tau:ℂ)‖≤tau.im/2)
    (hv : 4≤‖period v (tau:ℂ)‖) :
    ‖term a v z‖≤80*‖period v (tau:ℂ)‖^(-3:ℝ) := by
  by_cases hv0 : v=0
  · subst v
    norm_num [period] at hv
  · have hlo := (period_bounds tau v z hz).1
    have hb := PeriodPair.weierstrassP_bound 1 (by norm_num) a ha (period v z) (by linarith)
    have hr := Real.rpow_le_rpow_of_nonpos (by linarith : 0<‖period v (tau:ℂ)‖/2)
      hlo (by norm_num : (-3:ℝ)≤0)
    have hs : (‖period v (tau:ℂ)‖/2)^(-3:ℝ)=8*‖period v (tau:ℂ)‖^(-3:ℝ) := by
      rw [Real.rpow_neg (by positivity),Real.rpow_neg (norm_nonneg _)]
      simp only [Real.rpow_ofNat]
      field_simp
      <;> ring
    rw [hs] at hr
    simp only [term,hv0,if_false] at ⊢
    norm_num only [mul_one] at hb
    linarith

private def latticeSum (a : ℂ) (z : ℂ) : ℂ := ∑' v : Fin 2 → ℤ, term a v z

private theorem latticeSum_analyticAt (a : ℂ) (ha : ‖a‖ < 1)
    (hn : ∀ t : UpperHalfPlane, a ∉ (periods t).lattice) (tau : UpperHalfPlane) :
    AnalyticAt ℂ (latticeSum a) (tau:ℂ) := by
  let U : Set ℂ := Metric.ball (tau:ℂ) (tau.im/2) ∩ UpperHalfPlane.upperHalfPlaneSet
  have hU : IsOpen U := Metric.isOpen_ball.inter UpperHalfPlane.isOpen_upperHalfPlaneSet
  have ht : (tau:ℂ)∈U := ⟨by simp [half_pos tau.im_pos],tau.im_pos⟩
  have hc : TendstoUniformlyOn (fun s : Finset (Fin 2 → ℤ) => fun z => ∑v∈s, term a v z)
      (latticeSum a) atTop U := by
    apply tendstoUniformlyOn_tsum_of_cofinite_eventually (ThirdPeriodSummands318.majorant_summable tau)
    apply Filter.eventually_cofinite.mpr
    apply (small_periods_finite tau 4).subset
    intro v hv
    by_contra hbad
    have hlarge : 4≤‖period v (tau:ℂ)‖ := le_of_lt (lt_of_not_ge hbad)
    apply hv
    intro z hz
    exact term_bound a ha tau v z (le_of_lt (by simpa [dist_eq_norm] using hz.1)) hlarge
  have hf : DifferentiableOn ℂ (latticeSum a) U := hc.tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall (fun s => DifferentiableOn.fun_sum (fun v _ => by
      intro z hz
      let t : UpperHalfPlane := ⟨z,hz.2⟩
      exact (term_analyticAt a t (hn t) v).differentiableAt.differentiableWithinAt))) hU
  exact hf.analyticOnNhd hU (tau:ℂ) ht

private theorem latticeSum_eq (a : ℂ) (tau : UpperHalfPlane) :
    latticeSum a (tau:ℂ)=(periods tau).weierstrassPExcept 0 a := by
  rw [PeriodPair.weierstrassPExcept,←(latticeEquiv tau).tsum_eq]
  apply tsum_congr
  intro v
  change term a v (tau:ℂ)=
    if period v (tau:ℂ)=0 then 0 else 1/(a-period v (tau:ℂ))^2-1/(period v (tau:ℂ))^2
  by_cases hv : v=0
  · simp [term,hv,period]
  · simp [term,hv,period_ne_zero tau hv]

private theorem wp_eq (a : ℂ) (tau : UpperHalfPlane) :
    (periods tau).weierstrassP a = latticeSum a (tau:ℂ)+1/a^2 := by
  have he := (periods tau).weierstrassPExcept_add (0 : (periods tau).lattice) a
  simp only [ZeroMemClass.coe_zero,sub_zero,zero_pow (by decide : (2:ℕ) ≠ 0),div_zero] at he
  rw [← latticeSum_eq a tau] at he
  exact he.symm

private theorem wp_analyticAt (a : ℂ) (ha : ‖a‖ < 1)
    (hn : ∀ t : UpperHalfPlane, a ∉ (periods t).lattice) (tau : UpperHalfPlane) :
    AnalyticAt ℂ (fun z => (periods (UpperHalfPlane.ofComplex z)).weierstrassP a) (tau:ℂ) := by
  have he : (fun z => (periods (UpperHalfPlane.ofComplex z)).weierstrassP a)
      =ᶠ[𝓝 (tau:ℂ)] (fun z => latticeSum a z+1/a^2) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds tau.im_pos] with z hz
    change (periods (UpperHalfPlane.ofComplex (⟨z,hz⟩:UpperHalfPlane))).weierstrassP a =
      latticeSum a z+1/a^2
    rw [UpperHalfPlane.ofComplex_apply]
    exact wp_eq a ⟨z,hz⟩
  exact ((latticeSum_analyticAt a ha hn tau).add analyticAt_const).congr he.symm

private theorem marker_not_lattice (N : ℕ) [NeZero N] (hN : 1<N) (tau : UpperHalfPlane) :
    ((N:ℕ):ℂ)⁻¹ ∉ (periods tau).lattice := by
  intro hz
  have ho := MarkedPeriod318.standardPoint_order N tau
  rw [MarkedPeriod318.standardPoint_formula,LatticeModelPoint318.point_of_mem tau _ hz] at ho
  change addOrderOf (0 : (ModularWeierstrass318.curve tau).toAffine.Point)=N at ho
  have he : (1:ℕ)=N := by simpa using ho
  omega

/-- The actual arithmetic x of the simultaneous-sign orbit through the
primitive 1/N point, using the sign-independent short-model scale. -/
@[expose] def arithmeticX (N : ℕ) [NeZero N] (tau : UpperHalfPlane) : ℂ :=
  pointX (MarkedPeriod318.standardPoint N tau)/CanonicalXScale318.scale (tau : ℂ)

theorem arithmeticX_formula (N : ℕ) [NeZero N] (hN : 1<N) (tau : UpperHalfPlane) :
    arithmeticX N tau =
      ((periods tau).weierstrassP ((N:ℂ)⁻¹)/(2*(Real.pi:ℂ))^2)/
        CanonicalXScale318.scale (tau:ℂ) := by
  unfold arithmeticX
  rw [MarkedPeriod318.standardPoint_formula,
    LatticeModelPoint318.point_of_notMem tau _ (marker_not_lattice N hN tau)]
  rfl

/-- The pointwise comparison targets the actual arithmetic evaluation
fiber and the actual marked point, not an arbitrary solution for x.
The square scale is independent of the possible sign of the chosen iso. -/
theorem arithmeticX_in_arithmetic_fiber (N : ℕ) [NeZero N]
    (tau : UpperHalfPlane) (h : Admissible tau) :
    pointX ((OpenJAnalyticPoints318.pointAddEquiv N tau h).symm
      (MarkedPeriod318.standardPoint N tau)) = arithmeticX N tau := by
  have hs := OpenJAnalyticPoints318.scaling_spec N tau h
  rw [arithmeticX,CanonicalXScale318.scale_eq_square N tau h
    (OpenJAnalyticPoints318.scaling N tau h) hs.1 hs.2]
  generalize MarkedPeriod318.standardPoint N tau = P
  change pointX (ShortScaling318.pointInverse _ _ (OpenJAnalyticPoints318.scaling N tau h)
    hs.1 hs.2 P) = pointX P/(OpenJAnalyticPoints318.scaling N tau h:ℂ)^2
  cases P with
  | zero => simp [ShortScaling318.pointInverse,pointX]
  | some x y hxy => rfl

/-- Genuinely arbitrary level, not the existing level-three specialization.
This is the holomorphic algebraic x-coordinate candidate on the ordinary
j-disk; it does not assert a primitive-torsion coordinate algebra is built. -/
theorem arithmeticX_analyticAt (N : ℕ) [NeZero N] (hN : 1<N)
    (tau : UpperHalfPlane) (h : Admissible tau) :
    AnalyticAt ℂ (fun z => arithmeticX N (UpperHalfPlane.ofComplex z)) (tau:ℂ) := by
  have hNR : (1:ℝ)<(N:ℝ) := by exact_mod_cast hN
  have ha : ‖((N:ℂ)⁻¹)‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast,← one_div]
    apply (div_lt_iff₀ (by linarith : (0:ℝ)<(N:ℝ))).mpr
    simpa only [one_mul] using hNR
  have hw := ((wp_analyticAt ((N:ℂ)⁻¹) ha (marker_not_lattice N hN) tau).div_const
    (c := (2*(Real.pi:ℂ))^2)).div
      (CanonicalXScale318.scale_analyticAt N tau h) (CanonicalXScale318.scale_ne_zero N tau h)
  have he : (fun z => arithmeticX N (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝 (tau:ℂ)]
      (fun z => ((periods (UpperHalfPlane.ofComplex z)).weierstrassP ((N:ℂ)⁻¹)/
        (2*(Real.pi:ℂ))^2)/CanonicalXScale318.scale z) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds tau.im_pos] with z hz
    change arithmeticX N (UpperHalfPlane.ofComplex (⟨z,hz⟩:UpperHalfPlane)) = _
    rw [UpperHalfPlane.ofComplex_apply]
    exact arithmeticX_formula N hN ⟨z,hz⟩
  exact hw.congr he.symm

theorem arithmeticX_invariant (N : ℕ) [NeZero N] (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma1 N) (tau : UpperHalfPlane) :
    arithmeticX N (g•tau)=arithmeticX N tau := by
  have hp := (MarkedPeriod318.point_stabilizer N g tau).mpr hg
  have hs := scale_transform ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  change CanonicalXScale318.scale (g•tau:UpperHalfPlane)=_ at hs
  rw [arithmeticX,arithmeticX,← hp,pointX_transport,hs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (UpperHalfPlane.denom_ne_zero _ tau))

end SelectedMarkedPeriodCoordinate318
#print axioms SelectedMarkedPeriodCoordinate318.arithmeticX_in_arithmetic_fiber
#print axioms SelectedMarkedPeriodCoordinate318.arithmeticX_analyticAt
#print axioms SelectedMarkedPeriodCoordinate318.arithmeticX_invariant
