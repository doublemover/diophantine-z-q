module
public import PELOriginalWeierstrassCoordinates318
public section
noncomputable section
namespace WeierstrassInfinityChart318
open Complex Filter Topology
set_option maxHeartbeats 3000000
variable (P : PeriodPair)

/-- Genuine regularized homogeneous coordinates at the original lattice
pole. They tend to [0:-2:0], rather than using junk affine values at zero. -/
@[expose] def numeratorX (z : ℂ) : ℂ := z+z^3*P.weierstrassPExcept 0 z
@[expose] def denominatorY (z : ℂ) : ℂ := -2+z^3*P.derivWeierstrassPExcept 0 z
@[expose] def numeratorZ (z : ℂ) : ℂ := z^3
@[expose] def u (z : ℂ) : ℂ := numeratorX P z/denominatorY P z
@[expose] def v (z : ℂ) : ℂ := numeratorZ P z/denominatorY P z

lemma denominator_zero : denominatorY P 0=-2 := by simp [denominatorY]
lemma denominator_ne : denominatorY P 0≠0 := by rw [denominator_zero]; norm_num
lemma u_zero : u P 0=0 := by simp [u,numeratorX,denominatorY]
lemma v_zero : v P 0=0 := by simp [v,numeratorZ,denominatorY]

lemma numerator_analytic : AnalyticAt ℂ (numeratorX P) 0 := by
  have ha := P.analyticAt_weierstrassPExcept 0
  exact analyticAt_id.add ((analyticAt_id.pow 3).mul ha)
lemma denominator_analytic : AnalyticAt ℂ (denominatorY P) 0 := by
  have ha := P.analyticAt_derivWeierstrassPExcept 0
  exact analyticAt_const.add ((analyticAt_id.pow 3).mul ha)
lemma u_analytic : AnalyticAt ℂ (u P) 0 :=
  (numerator_analytic P).div (denominator_analytic P) (denominator_ne P)
lemma v_analytic : AnalyticAt ℂ (v P) 0 :=
  (analyticAt_id.pow 3).div (denominator_analytic P) (denominator_ne P)

lemma numerator_scaled (z : ℂ) (hz : z≠0) : numeratorX P z=z^3*P.weierstrassP z := by
  have h := P.weierstrassPExcept_add (0 : P.lattice) z
  simp only [Submodule.coe_zero,sub_zero,zero_pow (by decide : (2:ℕ)≠0),div_zero,sub_zero] at h
  rw [←h]
  unfold numeratorX
  field_simp [hz]
  ring
lemma denominator_scaled (z : ℂ) (hz : z≠0) : denominatorY P z=z^3*P.derivWeierstrassP z := by
  have h := P.derivWeierstrassPExcept_sub (0 : P.lattice) z
  simp only [Submodule.coe_zero,sub_zero] at h
  rw [←h]
  unfold denominatorY
  field_simp [hz]
  ring

/-- Exact overlap with the original affine Weierstrass coordinates.
The same nonzero homogeneous Y coordinate is used on both sides. -/
theorem affine_overlap (z : ℂ) (hz : z≠0) (hy : denominatorY P z≠0) :
    u P z=P.weierstrassP z/P.derivWeierstrassP z ∧
    v P z=1/P.derivWeierstrassP z := by
  have hp : P.derivWeierstrassP z≠0 := by
    intro h
    rw [denominator_scaled P z hz,h,mul_zero] at hy
    exact hy rfl
  constructor
  · rw [u,numerator_scaled P z hz,denominator_scaled P z hz]
    field_simp [hz,hp]
  · rw [v,numeratorZ,denominator_scaled P z hz]
    field_simp [hz,hp]

/-- The original projective cubic equation extends through the pole on
an ACTUAL neighborhood. At its center u=v=0 is the infinity point. -/
theorem cubic_eventually : ∀ᶠ z in 𝓝 (0:ℂ),
    v P z=4*u P z^3-P.g₂*u P z*v P z^2-P.g₃*v P z^3 := by
  have hy : ∀ᶠ z in 𝓝 (0:ℂ),denominatorY P z≠0 :=
    (denominator_analytic P).continuousAt.eventually (eventually_ne_nhds (denominator_ne P))
  filter_upwards [hy,P.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz hn
  by_cases hz0 : z=0
  · subst z
    simp [u_zero,v_zero]
  have hnl : z∉P.lattice := by
    intro h
    exact hn ⟨h,hz0⟩
  have hp : P.derivWeierstrassP z≠0 := by
    intro h
    rw [denominator_scaled P z hz0,h,mul_zero] at hz
    exact hz rfl
  obtain ⟨hu,hv⟩ := affine_overlap P z hz0 hz
  rw [hu,hv]
  have hc := P.derivWeierstrassP_sq z hnl
  field_simp [hp]
  linear_combination hc

/-- The infinity coordinate is genuinely nonsingular: u has derivative
-1/2 at the original lattice pole. This is not assumed from a model name. -/
theorem u_hasDerivAt : HasDerivAt (u P) (-1/2) 0 := by
  have ha := (P.analyticAt_weierstrassPExcept 0).differentiableAt.hasDerivAt
  have hb := (P.analyticAt_derivWeierstrassPExcept 0).differentiableAt.hasDerivAt
  have hpow := (hasDerivAt_id (0:ℂ)).pow 3
  have hx := (hasDerivAt_id (0:ℂ)).add (hpow.mul ha)
  have hy := (hasDerivAt_const (0:ℂ) (-2:ℂ)).add (hpow.mul hb)
  have h := hx.div hy (denominator_ne P)
  convert h using 1 <;> norm_num [u,numeratorX,denominatorY]
end WeierstrassInfinityChart318
