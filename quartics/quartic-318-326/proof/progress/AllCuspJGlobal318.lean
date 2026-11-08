module
public import AllCuspJPole318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 AllCuspCharts318 AllCuspJ318
open AllCuspQJ318
open scoped Manifold ContDiff
namespace AllCuspJGlobal318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual selected chart is the actual filled-disc chart at a cusp. -/
theorem chosen_at_cusp (N:ℕ) (hN:5≤N) (c:End N) :
    chosenChart N hN (cusp N hN c)=newChart N hN c := by
  classical
  have hc : cusp N hN c ∈ Set.range (cusp N hN) := ⟨c,rfl⟩
  have he : hc.choose=c := cusp_injective N hN hc.choose_spec
  simp only [chosenChart,dif_pos hc,he]

/-- Holomorphy expressed in the actual registered chart at any non-cusp point. -/
theorem chart_analytic_off_cusps (N:ℕ) (hN:5≤N) (z:Filled N hN)
    (hz:z∉Set.range (cusp N hN)) :
    AnalyticAt ℂ (filledJ N hN ∘ (chosenChart N hN z).symm) (chosenChart N hN z z) := by
  letI:=filledChartedSpace N hN
  letI:=AllCuspComplexCurve318.filled_isManifold N hN
  have he : chosenChart N hN z ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (Filled N hN) :=
    IsManifold.chart_mem_maximalAtlas z
  have hc := (contMDiffWithinAt_iff_source_of_mem_maximalAtlas he
    (chosenChart_source N hN z)).mp (AllCuspJHolomorphic318.holomorphic_off_cusps N hN z hz)
  have hd : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (filledJ N hN ∘ (chosenChart N hN z).symm) (chosenChart N hN z z) := by
    simpa only [OpenPartialHomeomorph.extend_coe,OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
      Function.comp_id,Set.preimage_univ,Set.range_id,Set.univ_inter,
      contMDiffWithinAt_univ] using hc
  exact hd.contDiffAt.analyticAt

/-- Global meromorphy in the chosen genuine complex chart at every point of the
actual compact curve, not just in independently supplied cusp germs. -/
theorem chart_meromorphic (N:ℕ) (hN:5≤N) (z:Filled N hN) :
    MeromorphicAt (filledJ N hN ∘ (chosenChart N hN z).symm) (chosenChart N hN z z) := by
  by_cases hz:z∈Set.range (cusp N hN)
  · obtain ⟨c,rfl⟩ := hz
    rw [chosen_at_cusp,AllCuspJPole318.cusp_coordinate_zero]
    exact AllCuspJPole318.cusp_meromorphic N hN c
  · exact (chart_analytic_off_cusps N hN z hz).meromorphicAt

/-- The negative-order locus is exactly the actual finite cusp complement. -/
theorem chart_pole_iff (N:ℕ) (hN:5≤N) (z:Filled N hN) :
    meromorphicOrderAt (filledJ N hN ∘ (chosenChart N hN z).symm)
      (chosenChart N hN z z) < 0 ↔ z∈Set.range (cusp N hN) := by
  constructor
  · intro hp
    by_contra hz
    exact (not_lt_of_ge (chart_analytic_off_cusps N hN z hz).meromorphicOrderAt_nonneg) hp
  · rintro ⟨c,rfl⟩
    rw [chosen_at_cusp,AllCuspJPole318.cusp_coordinate_zero]
    change meromorphicOrderAt (fun q:ℂ => filledJ N hN ((newChart N hN c).symm q)) 0 < 0
    rw [AllCuspJPole318.cusp_order]
    have hw : (0:ℤ) < (natWidth N hN c:ℤ) := by exact_mod_cast natWidth_pos N hN c
    exact_mod_cast neg_neg_of_pos hw

/-- There are finitely many poles, because they are precisely the already
constructed, distinctly embedded finite cusp type. -/
theorem finite_pole_locus (N:ℕ) (hN:5≤N) :
    Set.Finite {z:Filled N hN | meromorphicOrderAt
      (filledJ N hN ∘ (chosenChart N hN z).symm) (chosenChart N hN z z) < 0} := by
  have he : {z:Filled N hN | meromorphicOrderAt
      (filledJ N hN ∘ (chosenChart N hN z).symm) (chosenChart N hN z z) < 0} =
      Set.range (cusp N hN) := by
    ext z
    exact chart_pole_iff N hN z
  rw [he]
  letI : NeZero N := ⟨by omega⟩
  exact Set.finite_range _

end AllCuspJGlobal318
