module
public import AllCuspFilling318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318
namespace AllCuspCompact318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem smaller_radius (w:ℝ) (hw:0<w) : radius w 3<radius w 2 := by
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff_of_pos_right hw).mpr
  nlinarith [Real.pi_pos]

abbrev ClosedDisc (N:ℕ) (hN:5≤N) (c:End N) := Metric.closedBall (0:ℂ) (radius (width N hN c) 3)

@[expose] def closedInclusion (N:ℕ) (hN:5≤N) (c:End N) : ClosedDisc N hN c→disc N hN c :=
  fun q=>⟨q.val,lt_of_le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right] using q.property)
    (smaller_radius _ (width_pos N hN c))⟩

@[expose] def closedChart (N:ℕ) (hN:5≤N) (c:End N) : ClosedDisc N hN c→Filled N hN :=
  cuspChart N hN c ∘ closedInclusion N hN c

theorem closedChart_continuous (N:ℕ) (hN:5≤N) (c:End N) : Continuous (closedChart N hN c) :=
  (cuspChart_openEmbedding N hN c).continuous.comp (continuous_subtype_val.subtype_mk _)

theorem closedChart_compact (N:ℕ) (hN:5≤N) (c:End N) : IsCompact (Set.range (closedChart N hN c)) :=
  isCompact_range (closedChart_continuous N hN c)

theorem cusp_mem_closedChart (N:ℕ) (hN:5≤N) (c:End N) :
    cusp N hN c∈Set.range (closedChart N hN c) := by
  refine ⟨⟨0,?_⟩,rfl⟩
  simpa using (radius_positive (width N hN c) 3).le

theorem high_mem_closedChart (N:ℕ) (hN:5≤N) (c:End N) (b:Base (image N))
    (hb:b∈FiniteCuspCoverage318.cuspRegion N (representative N c) 3) :
    original N hN b∈Set.range (closedChart N hN c) := by
  obtain ⟨tau,htau,rfl⟩:=hb
  have ht2:tau∈high 2:=by change (2:ℝ)<tau.im;change (3:ℝ)<tau.im at htau;linarith
  let q:=qMap (width N hN c) 2 (width_pos N hN c) ⟨tau,ht2⟩
  have hq3:‖q.val‖<radius (width N hN c) 3:=
    (qParam_maps (width N hN c) 3 (width_pos N hN c) htau).2
  refine ⟨⟨q.val,by simpa only [Metric.mem_closedBall,dist_zero_right] using hq3.le⟩,?_⟩
  have hold:oldMap N hN ⟨c,q⟩=quotientMap N (representative N c•tau) := by
    change ((RotatedHomeomorph318.cuspHomeomorph N hN (representative N c)).symm q).val=_
    rw [show q=RotatedHomeomorph318.cuspHomeomorph N hN (representative N c)
      (RotatedProjection318.projection N (representative N c) ⟨tau,ht2⟩) from
      (RotatedHomeomorph318.cuspHomeomorph_projection N hN _ _).symm,
      Homeomorph.symm_apply_apply]
    rfl
  exact (original_oldMap N hN ⟨c,q⟩).symm.trans (congrArg (original N hN) hold)

/-- The entire actual all-cusp attachment is covered by a compact original
core and finitely many images of genuinely closed discs. -/
theorem compact_cover (N:ℕ) (hN:5≤N) :
    (Set.univ:Set (Filled N hN))=
      original N hN '' FiniteCuspCoverage318.compactCore N 3 ∪
        ⋃c:End N,Set.range (closedChart N hN c) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
    · rcases compact_core_and_distinct_ends N 3 b with hb|⟨c,hc⟩
      · exact Or.inl ⟨b,hb,rfl⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨c,high_mem_closedChart N hN c b hc⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨c,cusp_mem_closedChart N hN c⟩)
  · exact Set.subset_univ _

/-- Compactness is derived from the actual finite fundamental-domain cover,
not supplied as a compact-source premise. -/
theorem filled_compactSpace (N:ℕ) (hN:5≤N) : CompactSpace (Filled N hN) := by
  letI:NeZero N:=⟨by omega⟩
  apply isCompact_univ_iff.mp
  rw [compact_cover]
  exact ((FiniteCuspCoverage318.compactCore_isCompact N 3).image
    (original_openEmbedding N hN).continuous).union (isCompact_iUnion (closedChart_compact N hN))

end AllCuspCompact318
