module
public import ChordAlgebra318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ChordFlow318
open ChordAlgebra318
set_option maxHeartbeats 0

@[expose] def R (L : PeriodPair) (a b z : ℂ) : ℂ := chordX a b (L.weierstrassP z) (L.derivWeierstrassP z)
@[expose] def Y (L : PeriodPair) (a b z : ℂ) : ℂ := chordY a b (L.weierstrassP z) (L.derivWeierstrassP z)

lemma slope_hasDerivAt (L : PeriodPair) (a b z : ℂ) (hz : z ∉ L.lattice)
    (hx : L.weierstrassP z-a≠0) :
    HasDerivAt (fun w => slope a b (L.weierstrassP w) (L.derivWeierstrassP w))
      (slopeD a b L.g₂ (L.weierstrassP z) (L.derivWeierstrassP z)) z := by
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hd : HasDerivAt L.derivWeierstrassP (6*L.weierstrassP z^2-L.g₂/2) z := by
    rw [← WeierstrassODE318.second_derivative L z hz]
    exact (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  exact (hd.sub_const b).div (hp.sub_const a) hx

lemma R_hasDerivAt (L : PeriodPair) (a b z : ℂ) (hz : z ∉ L.lattice)
    (hx : L.weierstrassP z-a≠0) (hb : b^2=4*a^3-L.g₂*a-L.g₃) :
    HasDerivAt (R L a b) (Y L a b z) z := by
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hs := slope_hasDerivAt L a b z hz hx
  have hh := ((((hs.pow 2).div_const 4).sub hp).sub_const a)
  have he := first_flow a b L.g₂ L.g₃ (L.weierstrassP z) (L.derivWeierstrassP z) hx
    (L.derivWeierstrassP_sq z hz) hb
  convert hh using 1
  · rfl
  · dsimp only [Y]
    linear_combination -he

lemma Y_hasDerivAt (L : PeriodPair) (a b z : ℂ) (hz : z ∉ L.lattice)
    (hx : L.weierstrassP z-a≠0) (hb : b^2=4*a^3-L.g₂*a-L.g₃) :
    HasDerivAt (Y L a b) (6*(R L a b z)^2-L.g₂/2) z := by
  have hs := slope_hasDerivAt L a b z hz hx
  have hr := R_hasDerivAt L a b z hz hx hb
  have hh := (hasDerivAt_const z (-b)).sub (hs.mul (hr.sub_const a))
  have he := second_flow a b L.g₂ L.g₃ (L.weierstrassP z) (L.derivWeierstrassP z) hx
    (L.derivWeierstrassP_sq z hz) hb
  rw [first_flow a b L.g₂ L.g₃ (L.weierstrassP z) (L.derivWeierstrassP z) hx
    (L.derivWeierstrassP_sq z hz) hb] at he
  convert hh using 1
  · rfl
  · dsimp only [R,Y]
    linear_combination -he

lemma R_analytic (L : PeriodPair) (a b z : ℂ) (hz : z ∉ L.lattice)
    (hx : L.weierstrassP z-a≠0) : AnalyticAt ℂ (R L a b) z := by
  have hp := L.analyticOnNhd_weierstrassP z hz
  have hd := L.analyticOnNhd_derivWeierstrassP z hz
  unfold R chordX ChordAlgebra318.slope
  fun_prop

lemma R_second (L : PeriodPair) (a b z : ℂ) (hz : z ∉ L.lattice)
    (hx : L.weierstrassP z-a≠0) (hb : b^2=4*a^3-L.g₂*a-L.g₃) :
    deriv (deriv (R L a b)) z = 6*(R L a b z)^2-L.g₂/2 := by
  have hp : ContinuousAt (fun w => L.weierstrassP w-a) z :=
    (L.analyticOnNhd_weierstrassP z hz).continuousAt.sub continuousAt_const
  have he : deriv (R L a b) =ᶠ[𝓝 z] Y L a b := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
      hp.eventually_ne hx] with w hw hxw
    exact (R_hasDerivAt L a b w hw hxw hb).deriv
  rw [he.deriv_eq]
  exact (Y_hasDerivAt L a b z hz hx hb).deriv

lemma R_curve (L : PeriodPair) (a b z : ℂ) (hz : z ∉ L.lattice)
    (hx : L.weierstrassP z-a≠0) (hb : b^2=4*a^3-L.g₂*a-L.g₃) :
    (Y L a b z)^2 = 4*(R L a b z)^3-L.g₂*R L a b z-L.g₃ :=
  chord_curve a b L.g₂ L.g₃ (L.weierstrassP z) (L.derivWeierstrassP z) hx
    (L.derivWeierstrassP_sq z hz) hb

lemma exists_pair (L : PeriodPair) (x y : ℂ) (hc : y^2=4*x^3-L.g₂*x-L.g₃) :
    ∃ z : ℂ, z ∉ L.lattice ∧ L.weierstrassP z=x ∧ L.derivWeierstrassP z=y := by
  obtain ⟨z,hz,hx⟩ := WeierstrassSurjective318.exists_value L x
  have hsq := L.derivWeierstrassP_sq z hz
  rw [hx,← hc] at hsq
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hy | hy
  · exact ⟨z,hz,hx,hy⟩
  · refine ⟨-z,fun h => hz (neg_mem_iff.mp h),?_,?_⟩
    · simpa using hx
    · simp [hy]

end ChordFlow318
