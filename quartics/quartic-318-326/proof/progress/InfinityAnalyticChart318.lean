module
public import FiniteAnalyticCharts318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace InfinityAnalyticChart318
open PeriodEisenstein318 LatticeInvariants318 FiniteAnalyticCharts318
set_option maxHeartbeats 0

@[expose] def denominator (L : PeriodPair) (z : ℂ) : ℂ :=
  1-z^3*L.derivWeierstrassPExcept 0 z/2
@[expose] def parameter (L : PeriodPair) (z : ℂ) : ℂ :=
  z*(1+z^2*L.weierstrassPExcept 0 z)/denominator L z

lemma denominator_zero (L : PeriodPair) : denominator L 0=1 := by simp [denominator]
lemma parameter_zero (L : PeriodPair) : parameter L 0=0 := by simp [parameter]

lemma denominator_analytic (L : PeriodPair) : AnalyticAt ℂ (denominator L) 0 := by
  have hh := L.analyticAt_derivWeierstrassPExcept 0
  unfold denominator
  fun_prop

lemma parameter_analytic (L : PeriodPair) : AnalyticAt ℂ (parameter L) 0 := by
  have hh := L.analyticAt_weierstrassPExcept 0
  have hd := denominator_analytic L
  unfold parameter
  fun_prop (disch := simp [denominator_zero])

lemma parameter_hasDerivAt (L : PeriodPair) : HasDerivAt (parameter L) 1 0 := by
  have hh := L.analyticAt_weierstrassPExcept 0
  have hd := denominator_analytic L
  have ha : AnalyticAt ℂ (fun z : ℂ => (1+z^2*L.weierstrassPExcept 0 z)/denominator L z) 0 := by
    fun_prop (disch := simp [denominator_zero])
  have he := (hasDerivAt_id (0:ℂ)).mul ha.differentiableAt.hasDerivAt
  convert he using 1
  · funext z
    dsimp only [parameter,Pi.mul_apply,id_eq]
    ring
  · simp [denominator_zero]

lemma denominator_identity (L : PeriodPair) (z : ℂ) (hz : z≠0) :
    denominator L z= -z^3*L.derivWeierstrassP z/2 := by
  have he := L.derivWeierstrassPExcept_def (0 : L.lattice) z
  simp only [ZeroMemClass.coe_zero,sub_zero] at he
  rw [denominator,he]
  field_simp
  ring

lemma parameter_eq_ratio (L : PeriodPair) (z : ℂ) (hz : z≠0)
    (hd : L.derivWeierstrassP z≠0) : parameter L z= -2*L.weierstrassP z/L.derivWeierstrassP z := by
  have he := L.weierstrassPExcept_add (0 : L.lattice) z
  simp only [ZeroMemClass.coe_zero,sub_zero,zero_pow (by decide:2≠0),div_zero,sub_zero] at he
  rw [parameter,denominator_identity L z hz,← he]
  field_simp
  ring

lemma eventually_nonzero_derivative (L : PeriodPair) :
    ∀ᶠ z in 𝓝[≠] (0:ℂ), L.derivWeierstrassP z≠0 := by
  have hn := (denominator_analytic L).continuousAt.eventually_ne
    (by rw [denominator_zero]; exact one_ne_zero)
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hn] with z hz hd
  have hz0 : z≠0 := by simpa using hz
  rw [denominator_identity L z hz0] at hd
  intro he
  simp [he] at hd

/-- The actual normalized projective parameter -x/y, analytically filled at infinity. -/
@[expose] def t (tau : UpperHalfPlane) (z : ℂ) : ℂ :=
  (2*(Real.pi:ℂ))*parameter (periods tau) z

/-- The actual projective Z/Y coordinate, analytically filled at infinity. -/
@[expose] def v (tau : UpperHalfPlane) (z : ℂ) : ℂ :=
  -(2*(Real.pi:ℂ))^3*z^3/denominator (periods tau) z

lemma t_zero (tau : UpperHalfPlane) : t tau 0=0 := by simp [t,parameter_zero]
lemma v_zero (tau : UpperHalfPlane) : v tau 0=0 := by simp [v]
lemma t_analytic (tau : UpperHalfPlane) : AnalyticAt ℂ (t tau) 0 := by
  have ha := parameter_analytic (periods tau)
  unfold t
  fun_prop
lemma v_analytic (tau : UpperHalfPlane) : AnalyticAt ℂ (v tau) 0 := by
  have hd := denominator_analytic (periods tau)
  unfold v
  fun_prop (disch := simp [denominator_zero])

lemma t_hasDerivAt (tau : UpperHalfPlane) : HasDerivAt (t tau) (2*(Real.pi:ℂ)) 0 := by
  have hh := (hasDerivAt_const (0:ℂ) (2*(Real.pi:ℂ))).mul (parameter_hasDerivAt (periods tau))
  convert hh using 1
  · funext z
    rfl
  · simp

/-- Actual coordinate equalities in a punctured neighborhood of the point at infinity. -/
theorem coordinates_eventually (tau : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] (0:ℂ), yCoord tau z≠0 ∧
      t tau z= -xCoord tau z/yCoord tau z ∧ v tau z=1/yCoord tau z := by
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : 2*(Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) hp
  filter_upwards [self_mem_nhdsWithin,eventually_nonzero_derivative (periods tau)] with z hz hd
  have hz0 : z≠0 := by simpa using hz
  refine ⟨div_ne_zero hd (mul_ne_zero (by norm_num) (pow_ne_zero 3 hk)),?_,?_⟩
  · rw [t,parameter_eq_ratio (periods tau) z hz0 hd,xCoord,yCoord]
    field_simp
  · rw [v,denominator_identity (periods tau) z hz0,yCoord]
    field_simp

/-- A genuine holomorphic inverse to the actual normalized infinity parameter. -/
theorem exists_infinity_inverse (tau : UpperHalfPlane) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (fun z => g (t tau z)) =ᶠ[𝓝 0] id ∧
      (fun z => t tau (g z)) =ᶠ[𝓝 0] id ∧
      AnalyticAt ℂ (fun z => v tau (g z)) 0 := by
  have hp : deriv (t tau) 0≠0 := by
    rw [(t_hasDerivAt tau).deriv]
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  obtain ⟨g,hg,h0,hl,hr⟩ := analytic_inverse (t_analytic tau) hp
  rw [t_zero] at hg h0 hr
  refine ⟨g,hg,h0,hl,hr,?_⟩
  have hv : AnalyticAt ℂ (v tau) (g 0) := by rw [h0]; exact v_analytic tau
  exact hv.comp (f := g) hg
end InfinityAnalyticChart318
