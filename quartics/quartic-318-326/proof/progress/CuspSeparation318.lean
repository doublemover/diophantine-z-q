module
public import SingleCuspDensity318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 QuotientJ318 HighQParameter318 ActualCuspHomeomorph318
open ActualSingleCusp318
namespace CuspSeparation318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem qj_norm_tendsto : Tendsto (fun q:ℂ=>‖ActualQJ318.G q/q‖) (𝓝[≠] 0) atTop := by
  have hg : Tendsto (fun q:ℂ=>‖ActualQJ318.G q‖) (𝓝[≠] 0) (𝓝 1) := by
    have h : Tendsto ActualQJ318.G (𝓝[≠] 0) (𝓝 (ActualQJ318.G 0)) :=
      (ActualQJ318.G_differentiableAt 0 (by simp)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [ActualQJ318.G_zero,norm_one] using h.norm
  have hn : Tendsto (fun q:ℂ=>‖q‖) (𝓝[≠] 0) (𝓝[>] (0:ℝ)) := tendsto_norm_nhdsNE_zero
  simpa only [norm_div,div_eq_mul_inv,norm_mul,norm_inv,Pi.inv_apply] using
    Filter.Tendsto.pos_mul_atTop (by norm_num : (0:ℝ)<1) hg hn.inv_tendsto_nhdsGT_zero

theorem small_parameter_large_j (M:ℝ) : ∃epsilon:ℝ,0<epsilon ∧
    ∀q:ℂ,‖q‖<epsilon→q≠0→M<‖ActualQJ318.G q/q‖ := by
  obtain ⟨epsilon,hepsilon,h⟩ := Metric.mem_nhdsWithin_iff.mp
    (qj_norm_tendsto.eventually_gt_atTop M)
  refine ⟨epsilon,hepsilon,?_⟩
  intro q hq hne
  exact h ⟨by simpa using hq,hne⟩

theorem identification_j (N:ℕ) (b:Base (image N)) (q:disc)
    (he:original N b=cuspChart N q) :
    jMap N b=ActualQJ318.G q/(q:ℂ) := by
  obtain ⟨hb,hq⟩ := (TwoChartGluing318.left_eq_right_iff (overlap N) b q).mp he
  have hbs:b∈neighborhood N height := by rwa [overlap_source] at hb
  have hv:((overlap N b):ℂ)=ActualCuspPartialChart318.chart N b :=
    (ActualCuspPartialChart318.chart N).symm.subtypeRestr_symm_apply disc_nonempty hb
  have hc:(coordinate N ⟨b,hbs⟩:ℂ)=(q:ℂ) := hv.symm.trans (congrArg Subtype.val hq)
  have h := jMap_in_coordinate N ⟨b,hbs⟩
  simpa only [hc] using h

/-- Actual disjoint open neighborhoods separate the new cusp from every old
point. The proof uses the genuine j-growth, ruling out a doubled-origin gluing. -/
theorem separate_cusp (N:ℕ) (hN:5≤N) (b:Base (image N)) :
    ∃U V:Set (Filled N),IsOpen U ∧ IsOpen V ∧
      original N b∈U ∧ cusp N∈V ∧ Disjoint U V := by
  let M:ℝ:=‖jMap N b‖+1
  obtain ⟨epsilon,hepsilon,hlarge⟩ := small_parameter_large_j M
  let A:Set (Base (image N)) := {x | ‖jMap N x‖<M}
  let B:Set disc := {q | ‖(q:ℂ)‖<epsilon}
  have hA:IsOpen A := isOpen_lt (HolomorphicQuotientJ318.jMap_continuous N hN).norm continuous_const
  have hB:IsOpen B := isOpen_lt (continuous_subtype_val.norm) continuous_const
  refine ⟨original N '' A,cuspChart N '' B,
    (original_isOpenEmbedding N).isOpenMap _ hA,(cuspChart_isOpenEmbedding N).isOpenMap _ hB,
    ⟨b,by dsimp [A,M];linarith,rfl⟩,⟨zeroPoint,by simpa [B,zeroPoint] using hepsilon,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨q,hq,heq⟩
  have hne:(q:ℂ)≠0 := by
    intro hzero
    have hq0:q=zeroPoint := Subtype.ext hzero
    exact original_ne_cusp N x (heq.symm.trans (congrArg (cuspChart N) hq0))
  have hl:=hlarge q hq hne
  have hj:=identification_j N x q heq.symm
  rw [←hj] at hl
  exact (not_lt_of_ge hl.le) hx

end CuspSeparation318
