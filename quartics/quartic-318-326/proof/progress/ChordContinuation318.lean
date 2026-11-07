module
public import MeromorphicContinuation318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ChordContinuation318
open ChordAlgebra318 ChordFlow318
set_option maxHeartbeats 0

lemma R_meromorphic (L : PeriodPair) (a b : ℂ) : Meromorphic (R L a b) := by
  unfold R chordX ChordAlgebra318.slope
  fun_prop

lemma shifted_meromorphic (L : PeriodPair) (d : ℂ) :
    Meromorphic (fun z => L.weierstrassP (z+d)) := by
  intro z
  exact (L.meromorphic_weierstrassP (z+d)).comp_analyticAt
    (g := fun w : ℂ => w+d) (by fun_prop)

lemma shifted_second (L : PeriodPair) (d z : ℂ) (hz : z+d ∉ L.lattice) :
    deriv (deriv (fun w => L.weierstrassP (w+d))) z =
      6*(L.weierstrassP (z+d))^2-L.g₂/2 := by
  have he : deriv (fun w => L.weierstrassP (w+d)) =
      (fun w => L.derivWeierstrassP (w+d)) := by
    funext w
    simp [deriv_comp_add_const]
  rw [he,deriv_comp_add_const,WeierstrassODE318.second_derivative L (z+d) hz]

/-- The rational chord coordinate is an actual translate of ℘ as a meromorphic germ.
The translation is constructed from actual surjectivity, not supplied. -/
theorem exists_translation_germ (L : PeriodPair) (a b : ℂ)
    (hb : b^2=4*a^3-L.g₂*a-L.g₃) :
    ∃ z d : ℂ, R L a b =ᶠ[𝓝 z] (fun w => L.weierstrassP (w+d)) := by
  obtain ⟨z,hz,hx⟩ := WeierstrassSurjective318.exists_value L (a+1)
  have hx' : L.weierstrassP z-a≠0 := by rw [hx]; ring_nf; exact one_ne_zero
  obtain ⟨u,hu,huX,huY⟩ := exists_pair L (R L a b z) (Y L a b z) (R_curve L a b z hz hx' hb)
  let d := u-z
  have hzd : z+d=u := by dsimp [d]; ring
  have hga : AnalyticAt ℂ (fun w => L.weierstrassP (w+d)) z := by
    have ha : AnalyticAt ℂ L.weierstrassP (z+d) := hzd ▸ L.analyticOnNhd_weierstrassP u hu
    exact ha.comp (f := fun w : ℂ => w+d) (by fun_prop)
  have hF : deriv (deriv (R L a b)) =ᶠ[𝓝 z]
      (fun w => 6*(R L a b w*R L a b w)+(-L.g₂/2)) := by
    have hp : ContinuousAt (fun w => L.weierstrassP w-a) z :=
      (L.analyticOnNhd_weierstrassP z hz).continuousAt.sub continuousAt_const
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,hp.eventually_ne hx'] with w hw hxw
    rw [R_second L a b w hw hxw hb]
    ring
  have hG : deriv (deriv (fun w => L.weierstrassP (w+d))) =ᶠ[𝓝 z]
      (fun w => 6*(L.weierstrassP (w+d)*L.weierstrassP (w+d))+(-L.g₂/2)) := by
    have hzu : z+d ∉ L.lattice := hzd ▸ hu
    have hn : ∀ᶠ w in 𝓝 z, w+d ∉ L.lattice :=
      (by fun_prop : ContinuousAt (fun w : ℂ => w+d) z).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds hzu)
    filter_upwards [hn] with w hw
    rw [shifted_second L d w hw]
    ring
  refine ⟨z,d,AnalyticODEUniqueness318.quadratic_germ_unique (R_analytic L a b z hz hx') hga
    hF hG ?_ ?_⟩
  · rw [hzd]
    exact huX.symm
  · rw [(R_hasDerivAt L a b z hz hx' hb).deriv,deriv_comp_add_const,L.deriv_weierstrassP,hzd]
    exact huY.symm

end ChordContinuation318
