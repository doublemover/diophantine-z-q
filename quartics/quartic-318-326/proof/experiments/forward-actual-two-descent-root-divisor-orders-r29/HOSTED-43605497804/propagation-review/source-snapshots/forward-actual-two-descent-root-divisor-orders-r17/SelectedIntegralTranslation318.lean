module
public import SelectedTraceFromDepths318
public section
noncomputable section
namespace SelectedIntegralTranslation318
open ConcreteG8Domain ConcretePadic318 ValuativeOrbitBounds318
open CoherentMultipleCharts318 (chartU chartV)
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- Translation of a near-identity point by an integral reciprocal chart
has integral u-coordinate. The actual addition denominator is a unit. -/
theorem integral_translate {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (D u w a b : F) (hD : Bound v 0 D) (hu : Bound v 0 u) (hw : Bound v 0 w)
    (hn : Near v 1 a b) : Bound v 0 (ReciprocalGroup318.sumU D u w a b) := by
  have hT : Bound v 2 (D*u^2*a^2) := by
    have he := bmul v (bmul_unit v hD (bsquare v hu)) (bsquare v hn.1)
    simpa only [mul_zero,zero_add,mul_one] using he
  have hden : v (1+D*u^2*a^2)=0 :=
    one_near_unit v (by norm_num : (0:ℤ)<2) (by simpa only [add_sub_cancel_left] using hT)
  have hb : Bound v 0 b := by rw [Bound,one_near_unit v (by norm_num) hn.2]
  have ha : Bound v 0 a := weaken v hn.1 (by norm_num)
  exact bdiv v (badd v (bmul_unit v hu hb) (bmul_unit v ha hw)) hden

lemma sqrt_two_unit (p : ℕ) [Fact p.Prime] (hp : 3≤p) (rho : ℚ_[p]) (hr : rho^2=2) :
    place p rho hr i=0 := by
  have hi : i≠0 := by
    intro he
    have hh := congrArg QuadraticAlgebra.im he
    norm_num [i,pair] at hh
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp (((place p rho hr).ne_top_iff).mpr hi)
  have hs := congrArg (place p rho hr) i_square
  rw [(place p rho hr).map_pow,←ha,SelectedPositiveDelta318.two_unit p hp rho hr] at hs
  have he : 2*a=0 := by exact_mod_cast hs
  have hz : a=0 := by omega
  simpa [hz] using ha.symm

/-- Original coherent chart at index1 is integral at all selected primes;
its only displayed denominators are41 and1681. -/
theorem one_integral (p : ℕ) [Fact p.Prime] (hp : 76176<p)
    (rho : ℚ_[p]) (hr : rho^2=2) :
    Bound (place p rho hr) 0 (chartU 1) ∧ Bound (place p rho hr) 0 (chartV 1) := by
  let v := place p rho hr
  have hi : Bound v 0 i := by rw [Bound,sqrt_two_unit p (by omega) rho hr]
  have h41 : v (41:K)=0 := by
    have he : (41:K)=pair 41 0 := rfl
    rw [he,place_rational]
    exact SelectedContactWeightValues318.small_unit p 41 (by norm_num) (by omega)
  have h1681 : v (1681:K)=0 := by
    have he : (1681:K)=pair 1681 0 := rfl
    rw [he,place_rational]
    exact SelectedContactWeightValues318.small_unit p 1681 (by norm_num) (by omega)
  have hu : chartU 1=((8:K)+14*i)/41 := by
    rw [GeneratorScalarProgression318.chartU_one]
    apply (eq_div_iff (by norm_num : (41:K)≠0)).mpr
    ext <;> norm_num [pair,i]
  have hv : chartV 1=((207:K)-960*i)/1681 := by
    rw [ActualSeventeenEntry318.actual1.2]
    apply (eq_div_iff (by norm_num : (1681:K)≠0)).mpr
    ext <;> norm_num [ActualSeventeenEntry318.v1,pair,i]
  constructor
  · rw [hu]
    exact bdiv v (badd v (bnat v 8) (bmul_unit v (bnat v 14) hi)) h41
  · rw [hv]
    exact bdiv v (bsub v (bnat v 207) (bmul_unit v (bnat v 960) hi)) h1681

/-- The same congruences give the other two INTEGRAL chart factors needed
by the actual rational norms: primary h−1 and opposite h. -/
theorem opposite_factors (p : ℕ) [Fact p.Prime] (hp : 76176<p)
    (rho : ℚ_[p]) (hr : rho^2=2) (h : ℤ)
    (hm : Near (place p rho hr) 4 (chartU h) (chartV h))
    (hp' : Near (place p (-rho) (negative_root p rho hr)) 1 (chartU (h-1)) (chartV (h-1))) :
    Bound (place p rho hr) 0 (chartU (h-1)) ∧
    Bound (place p (-rho) (negative_root p rho hr)) 0 (chartU h) := by
  have h1m := one_integral p hp rho hr
  have h1p := one_integral p hp (-rho) (negative_root p rho hr)
  constructor
  · have hn : Near (place p rho hr) 1 (chartU h) (chartV h) :=
      ⟨weaken _ hm.1 (by norm_num),weaken _ hm.2 (by norm_num)⟩
    have he := integral_translate (place p rho hr) D (chartU (-1)) (chartV (-1))
      (chartU h) (chartV h) (ActualSplitOrbitEntry318.coefficient_bound p rho hr)
      (by simpa only [CoherentMultipleCharts318.chartU_negative] using bneg _ h1m.1)
      (by simpa only [CoherentMultipleCharts318.chartV_negative] using h1m.2) hn
    rw [←CoherentAdditionV318.chartU_add] at he
    simpa only [show (-1:ℤ)+h=h-1 by omega] using he
  · have he := integral_translate (place p (-rho) (negative_root p rho hr)) D
      (chartU 1) (chartV 1) (chartU (h-1)) (chartV (h-1))
      (ActualSplitOrbitEntry318.coefficient_bound p (-rho) _) h1p.1 h1p.2 hp'
    rw [←CoherentAdditionV318.chartU_add] at he
    simpa only [show (1:ℤ)+(h-1)=h by omega] using he

end SelectedIntegralTranslation318
