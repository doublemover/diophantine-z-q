module
public import LinearScalingGerm318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ScaledPeriodLattice318
open PeriodEisenstein318 LatticeInvariants318 LinearScalingGerm318
set_option maxHeartbeats 0

lemma scaled_wp_germ (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve sigma).a₄=(u:ℂ)^4*(ModularWeierstrass318.curve tau).a₄)
    (h6 : (ModularWeierstrass318.curve sigma).a₆=(u:ℂ)^6*(ModularWeierstrass318.curve tau).a₆) :
    (fun z => (periods sigma).weierstrassP ((u:ℂ)⁻¹*z)) =ᶠ[𝓝 0]
      (fun z => (u:ℂ)^2*(periods tau).weierstrassP z) := by
  have he := (linear_coordinate_germs tau sigma u h4 h6).1
  have hk : (2*(Real.pi:ℂ))^2≠0 := pow_ne_zero 2
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  filter_upwards [he] with z hz
  unfold xCoord at hz
  apply (div_left_inj' hk).mp
  simpa only [mul_div_assoc] using hz

/-- Analytic continuation of the genuine scaling germ across the complement of
both actual lattices. No elliptic-curve classification theorem is assumed. -/
theorem scaled_wp_eq_on (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve sigma).a₄=(u:ℂ)^4*(ModularWeierstrass318.curve tau).a₄)
    (h6 : (ModularWeierstrass318.curve sigma).a₆=(u:ℂ)^6*(ModularWeierstrass318.curve tau).a₆) :
    ∀ z : ℂ, z ∉ (periods tau).lattice → (u:ℂ)⁻¹*z ∉ (periods sigma).lattice →
      (periods sigma).weierstrassP ((u:ℂ)⁻¹*z)=(u:ℂ)^2*(periods tau).weierstrassP z := by
  let S : Set ℂ := (((periods tau).lattice : Set ℂ) ∪
    ((fun z : ℂ => (u:ℂ)⁻¹*z) ⁻¹' (periods sigma).lattice))ᶜ
  have hS (z : ℂ) : z∈S ↔ z ∉ (periods tau).lattice ∧ (u:ℂ)⁻¹*z ∉ (periods sigma).lattice := by
    simp [S]
  have hc1 : ((periods tau).lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := (periods tau).lattice)
  have hc2 : ((periods sigma).lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := (periods sigma).lattice)
  have hi : Function.Injective (fun z : ℂ => (u:ℂ)⁻¹*z) :=
    mul_right_injective₀ (inv_ne_zero (Units.ne_zero u))
  have hc : IsPreconnected S :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (hc1.union (hc2.preimage hi))).isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z => (periods sigma).weierstrassP ((u:ℂ)⁻¹*z)) S := by
    intro z hz
    exact ((periods sigma).analyticOnNhd_weierstrassP _ ((hS z).mp hz).2).comp
      (f := fun z : ℂ => (u:ℂ)⁻¹*z) (by fun_prop)
  have hg : AnalyticOnNhd ℂ (fun z => (u:ℂ)^2*(periods tau).weierstrassP z) S := by
    intro z hz
    exact analyticAt_const.mul ((periods tau).analyticOnNhd_weierstrassP _ ((hS z).mp hz).1)
  have hlin : AnalyticAt ℂ (fun z : ℂ => (u:ℂ)⁻¹*z) 0 := by fun_prop
  have ht := ScaledCoordinateGerm318.tendsto_puncture hlin (by simp)
    (by simpa using (hasDerivAt_id (0:ℂ)).const_mul ((u:ℂ)⁻¹))
    (inv_ne_zero (Units.ne_zero u))
  have hnear : ∀ᶠ z in 𝓝[≠] (0:ℂ), z∈S ∧
      (fun w => (periods sigma).weierstrassP ((u:ℂ)⁻¹*w)) =ᶠ[𝓝 z]
        (fun w => (u:ℂ)^2*(periods tau).weierstrassP w) := by
    filter_upwards [regular_eventually tau,ht.eventually (regular_eventually sigma),
      mem_nhdsWithin_of_mem_nhds (scaled_wp_germ tau sigma u h4 h6).eventuallyEq_nhds]
      with z hzt hzs he
    exact ⟨(hS z).mpr ⟨hzt,hzs⟩,he⟩
  obtain ⟨z,hz,he⟩ := hnear.exists
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hc hz he
  exact fun z hzt hzs => heq ((hS z).mpr ⟨hzt,hzs⟩)

lemma lattice_inclusion_of_wp_eq (L M : PeriodPair) (c d : ℂ)
    (he : ∀ z : ℂ, z ∉ L.lattice → c*z ∉ M.lattice →
      L.weierstrassP z=d*M.weierstrassP (c*z)) :
    ∀ l : ℂ, l∈L.lattice → c*l∈M.lattice := by
  intro l hl
  by_contra hn
  have hc : ContinuousAt (fun z => d*M.weierstrassP (c*z)) l := by
    have ha := (M.analyticOnNhd_weierstrassP (c*l) hn).comp
      (f := fun z : ℂ => c*z) (by fun_prop)
    exact (analyticAt_const.mul ha).continuousAt
  have hnear : ∀ᶠ z in 𝓝 l, c*z ∉ M.lattice :=
    (by fun_prop : ContinuousAt (fun z : ℂ => c*z) l).eventually
      (M.isClosed_lattice.isOpen_compl.mem_nhds hn)
  have hEq : L.weierstrassP =ᶠ[𝓝[≠] l] (fun z => d*M.weierstrassP (c*z)) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds
      (L.compl_lattice_sdiff_singleton_mem_nhds l),mem_nhdsWithin_of_mem_nhds hnear]
      with z hz hzl hzm
    apply he z _ hzm
    simp only [mem_compl_iff,Set.mem_sdiff,SetLike.mem_coe,mem_singleton_iff] at hz hzl ⊢
    aesop
  have ht : Tendsto L.weierstrassP (𝓝[≠] l) (𝓝 (d*M.weierstrassP (c*l))) :=
    (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' hEq.symm
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (L.meromorphic_weierstrassP l)).mp
    ⟨d*M.weierstrassP (c*l),ht⟩
  rw [L.order_weierstrassP l hl] at ho
  exact (by decide : ¬(0:WithTop ℤ)≤ -2) ho

/-- Actual short-model scaling forces actual period-lattice homothety. -/
theorem lattice_homothety (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (h4 : (ModularWeierstrass318.curve sigma).a₄=(u:ℂ)^4*(ModularWeierstrass318.curve tau).a₄)
    (h6 : (ModularWeierstrass318.curve sigma).a₆=(u:ℂ)^6*(ModularWeierstrass318.curve tau).a₆) :
    ∀ z : ℂ, z∈(periods tau).lattice ↔ (u:ℂ)⁻¹*z∈(periods sigma).lattice := by
  have he := scaled_wp_eq_on tau sigma u h4 h6
  have hf := lattice_inclusion_of_wp_eq (periods tau) (periods sigma) ((u:ℂ)⁻¹) (((u:ℂ)⁻¹)^2)
    (by
      intro z hzt hzs
      rw [he z hzt hzs]
      field_simp
      <;> ring)
  have hr := lattice_inclusion_of_wp_eq (periods sigma) (periods tau) (u:ℂ) ((u:ℂ)^2)
    (by
      intro z hzs hzt
      have hz := he ((u:ℂ)*z) hzt (by simpa using hzs)
      simpa using hz)
  intro z
  constructor
  · exact hf z
  · intro hz
    simpa using hr ((u:ℂ)⁻¹*z) hz

end ScaledPeriodLattice318
