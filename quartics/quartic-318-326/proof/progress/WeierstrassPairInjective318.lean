module
public import AnalyticODEUniqueness318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace WeierstrassPairInjective318
set_option maxHeartbeats 0

lemma translated_germ (L : PeriodPair) (z d : ℂ)
    (hz : z ∉ L.lattice) (hzd : z+d ∉ L.lattice)
    (h0 : L.weierstrassP z = L.weierstrassP (z+d))
    (h1 : L.derivWeierstrassP z = L.derivWeierstrassP (z+d)) :
    L.weierstrassP =ᶠ[𝓝 z] (fun w => L.weierstrassP (w+d)) := by
  have hf := L.analyticOnNhd_weierstrassP z hz
  have hg : AnalyticAt ℂ (fun w => L.weierstrassP (w+d)) z :=
    (L.analyticOnNhd_weierstrassP (z+d) hzd).comp (f := fun w : ℂ => w+d) (by fun_prop)
  have hF : deriv (deriv L.weierstrassP) =ᶠ[𝓝 z]
      (fun w => 6*(L.weierstrassP w * L.weierstrassP w) + (-L.g₂/2)) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    rw [L.deriv_weierstrassP, WeierstrassODE318.second_derivative L w hw]
    ring
  have hG : deriv (deriv (fun w => L.weierstrassP (w+d))) =ᶠ[𝓝 z]
      (fun w => 6*(L.weierstrassP (w+d) * L.weierstrassP (w+d)) + (-L.g₂/2)) := by
    have hn : ∀ᶠ w in 𝓝 z, w+d ∉ L.lattice :=
      (by fun_prop : ContinuousAt (fun w : ℂ => w+d) z).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds hzd)
    filter_upwards [hn] with w hw
    have he : deriv (fun w => L.weierstrassP (w+d)) =
        (fun w => L.derivWeierstrassP (w+d)) := by
      funext t
      simp [deriv_comp_add_const]
    rw [he, deriv_comp_add_const, WeierstrassODE318.second_derivative L (w+d) hw]
    ring
  apply AnalyticODEUniqueness318.quadratic_germ_unique hf hg hF hG h0
  simpa [deriv_comp_add_const] using h1

lemma translated_eq_on (L : PeriodPair) (z d : ℂ)
    (hz : z ∉ L.lattice) (hzd : z+d ∉ L.lattice)
    (h0 : L.weierstrassP z = L.weierstrassP (z+d))
    (h1 : L.derivWeierstrassP z = L.derivWeierstrassP (z+d)) :
    ∀ w, w ∉ L.lattice → w+d ∉ L.lattice →
      L.weierstrassP w = L.weierstrassP (w+d) := by
  let S : Set ℂ := ((L.lattice : Set ℂ) ∪ ((fun w : ℂ => w+d) ⁻¹' L.lattice))ᶜ
  have hS (w : ℂ) : w ∈ S ↔ w ∉ L.lattice ∧ w+d ∉ L.lattice := by
    simp [S]
  have hcnt : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hc : IsPreconnected S :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (hcnt.union (hcnt.preimage (add_left_injective d)))).isPreconnected
  have hf : AnalyticOnNhd ℂ L.weierstrassP S :=
    fun w hw => L.analyticOnNhd_weierstrassP w ((hS w).mp hw).1
  have hg : AnalyticOnNhd ℂ (fun w => L.weierstrassP (w+d)) S :=
    fun w hw => (L.analyticOnNhd_weierstrassP (w+d) ((hS w).mp hw).2).comp (f := fun w : ℂ => w+d) (by fun_prop)
  have he := hf.eqOn_of_preconnected_of_eventuallyEq hg hc ((hS z).mpr ⟨hz,hzd⟩)
    (translated_germ L z d hz hzd h0 h1)
  exact fun w hw hwd => he ((hS w).mpr ⟨hw,hwd⟩)

/-- Equality of the actual ℘ pair forces the translation to be an actual lattice period. -/
theorem pair_equality_forces_period (L : PeriodPair) (z d : ℂ)
    (hz : z ∉ L.lattice) (hzd : z+d ∉ L.lattice)
    (h0 : L.weierstrassP z = L.weierstrassP (z+d))
    (h1 : L.derivWeierstrassP z = L.derivWeierstrassP (z+d)) : d ∈ L.lattice := by
  by_contra hd
  have hc : ContinuousAt (fun w => L.weierstrassP (w+d)) 0 := by
    have ha : AnalyticAt ℂ L.weierstrassP (0+d) := by
      simpa only [zero_add] using L.analyticOnNhd_weierstrassP d hd
    exact ha.continuousAt.comp (f := fun w : ℂ => w+d) (by fun_prop : ContinuousAt (fun w : ℂ => w+d) 0)
  have hn : ∀ᶠ w in 𝓝 (0 : ℂ), w+d ∉ L.lattice := by
    have hh : ContinuousAt (fun w : ℂ => w+d) 0 := by fun_prop
    have hevent : ∀ᶠ y in 𝓝 (0+d), y ∉ L.lattice := by
      change (L.lattice : Set ℂ)ᶜ ∈ 𝓝 (0+d)
      simpa only [zero_add] using L.isClosed_lattice.isOpen_compl.mem_nhds hd
    exact hh.eventually hevent
  have he : L.weierstrassP =ᶠ[𝓝[≠] (0:ℂ)] (fun w => L.weierstrassP (w+d)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      mem_nhdsWithin_of_mem_nhds hn] with w hw hwl hwd
    have hw' : w ∉ L.lattice := by
      simp only [mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe, mem_singleton_iff] at hw hwl ⊢
      aesop
    exact translated_eq_on L z d hz hzd h0 h1 w hw' hwd
  have ht : Tendsto L.weierstrassP (𝓝[≠] (0:ℂ)) (𝓝 (L.weierstrassP d)) := by
    simpa only [zero_add] using (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (L.meromorphic_weierstrassP 0)).mp
    ⟨L.weierstrassP d, ht⟩
  rw [L.order_weierstrassP 0 L.lattice.zero_mem] at ho
  have hh : ¬ (0 : WithTop ℤ) ≤ -2 := by decide
  exact hh ho

/-- The actual pair separates non-lattice points modulo the period lattice. -/
theorem pair_eq_iff_sub_mem (L : PeriodPair) (z w : ℂ)
    (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    (L.weierstrassP z = L.weierstrassP w ∧
      L.derivWeierstrassP z = L.derivWeierstrassP w) ↔ w-z ∈ L.lattice := by
  constructor
  · intro h
    apply pair_equality_forces_period L z (w-z) hz
    · simpa using hw
    · simpa using h.1
    · simpa using h.2
  · intro h
    have h0 := L.weierstrassP_add_coe z ⟨w-z,h⟩
    have h1 := L.derivWeierstrassP_add_coe z ⟨w-z,h⟩
    exact ⟨by simpa using h0.symm, by simpa using h1.symm⟩
end WeierstrassPairInjective318
