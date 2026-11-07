module
public import ChordPole318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace WeierstrassChord318
open ChordAlgebra318 ChordFlow318 ChordContinuation318 ChordPole318
set_option maxHeartbeats 0

lemma sum_not_mem (L : PeriodPair) (z w : ℂ)
    (hx : L.weierstrassP z-L.weierstrassP w≠0) : z+w ∉ L.lattice := by
  intro hm
  have he := L.weierstrassP_add_coe (-w) ⟨z+w,hm⟩
  have he' : L.weierstrassP z=L.weierstrassP w := by simpa using he
  exact hx (sub_eq_zero.mpr he')

/-- The actual chord's initially unknown translation is forced to be the second point by its pole. -/
lemma chord_germ (L : PeriodPair) (w : ℂ) (hw : w ∉ L.lattice)
    (hb : L.derivWeierstrassP w≠0) :
    ∃ z : ℂ, R L (L.weierstrassP w) (L.derivWeierstrassP w) =ᶠ[𝓝 z]
      (fun v => L.weierstrassP (v+w)) := by
  obtain ⟨z,d,he⟩ := exists_translation_germ L (L.weierstrassP w) (L.derivWeierstrassP w)
    (L.derivWeierstrassP_sq w hw)
  have hpunct := MeromorphicContinuation318.punctured_eq
    (R_meromorphic L _ _) (shifted_meromorphic L d) he (-w)
  have hdm : d-w ∈ L.lattice := by
    by_contra hdm
    have ha : AnalyticAt ℂ L.weierstrassP (-w+d) :=
      L.analyticOnNhd_weierstrassP (-w+d) (by simpa [sub_eq_add_neg,add_comm] using hdm)
    have hg : AnalyticAt ℂ (fun v => L.weierstrassP (v+d)) (-w) :=
      ha.comp (f := fun v : ℂ => v+d) (by fun_prop)
    have ho := hg.meromorphicOrderAt_nonneg
    rw [← meromorphicOrderAt_congr hpunct,R_order_inverse L w hw hb] at ho
    exact (by decide : ¬(0:WithTop ℤ)≤-2) ho
  have hfun : (fun v => L.weierstrassP (v+d))=(fun v => L.weierstrassP (v+w)) := by
    funext v
    have hh := L.weierstrassP_add_coe (v+w) ⟨d-w,hdm⟩
    simpa [add_assoc] using hh
  exact ⟨z,hfun ▸ he⟩

/-- Genuine Weierstrass chord addition formula on the ordinary chord locus. -/
theorem chord_pair (L : PeriodPair) (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z-L.weierstrassP w≠0) (hb : L.derivWeierstrassP w≠0) :
    R L (L.weierstrassP w) (L.derivWeierstrassP w) z=L.weierstrassP (z+w) ∧
      Y L (L.weierstrassP w) (L.derivWeierstrassP w) z=L.derivWeierstrassP (z+w) := by
  obtain ⟨u,he⟩ := chord_germ L w hw hb
  have hf := (R_analytic L (L.weierstrassP w) (L.derivWeierstrassP w) z hz hx).continuousAt
  have hg : AnalyticAt ℂ (fun v => L.weierstrassP (v+w)) z :=
    (L.analyticOnNhd_weierstrassP (z+w) (sum_not_mem L z w hx)).comp
      (f := fun v : ℂ => v+w) (by fun_prop)
  have heq := MeromorphicContinuation318.punctured_eq (R_meromorphic L _ _)
    (shifted_meromorphic L w) he z
  have hfull := (hf.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).mp heq
  refine ⟨hfull.self_of_nhds,?_⟩
  have hd := hfull.deriv_eq
  rw [(R_hasDerivAt L _ _ z hz hx (L.derivWeierstrassP_sq w hw)).deriv,
    deriv_comp_add_const,L.deriv_weierstrassP] at hd
  exact hd

end WeierstrassChord318
