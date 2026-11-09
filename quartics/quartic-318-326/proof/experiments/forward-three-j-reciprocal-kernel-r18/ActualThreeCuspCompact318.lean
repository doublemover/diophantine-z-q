module
public import ActualThreeCuspFilling318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 ActualThreeCuspOverlap318 ActualThreeCuspFilling318
namespace ActualThreeCuspCompact318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem smaller_radius (w:ℝ) (hw:0<w) : radius w 3<radius w 2 := by
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff_of_pos_right hw).mpr
  nlinarith [Real.pi_pos]

abbrev ClosedDisc (c:End 3) := Metric.closedBall (0:ℂ) (radius (width c) 3)

@[expose] def closedInclusion (c:End 3) : ClosedDisc c→disc c :=
  fun q=>⟨q.val,lt_of_le_of_lt (by simpa only [Metric.mem_closedBall,dist_zero_right] using q.property)
    (smaller_radius _ (width_pos c))⟩

@[expose] def closedChart (c:End 3) : ClosedDisc c→Filled :=
  cuspChart c ∘ closedInclusion c

theorem closedChart_continuous (c:End 3) : Continuous (closedChart c) :=
  (cuspChart_openEmbedding c).continuous.comp (continuous_subtype_val.subtype_mk _)

theorem closedChart_compact (c:End 3) : IsCompact (Set.range (closedChart c)) :=
  isCompact_range (closedChart_continuous c)

theorem cusp_mem_closedChart (c:End 3) :
    cusp c∈Set.range (closedChart c) := by
  refine ⟨⟨0,?_⟩,rfl⟩
  simpa using (radius_positive (width c) 3).le

theorem high_mem_closedChart (c:End 3) (b:Base (image 3))
    (hb:b∈FiniteCuspCoverage318.cuspRegion 3 (representative 3 c) 3) :
    original b∈Set.range (closedChart c) := by
  obtain ⟨tau,htau,rfl⟩:=hb
  have ht2:tau∈high 2:=by change (2:ℝ)<tau.im;change (3:ℝ)<tau.im at htau;linarith
  let q:=qMap (width c) 2 (width_pos c) ⟨tau,ht2⟩
  have hq3:‖q.val‖<radius (width c) 3:=
    (qParam_maps (width c) 3 (width_pos c) htau).2
  refine ⟨⟨q.val,by simpa only [Metric.mem_closedBall,dist_zero_right] using hq3.le⟩,?_⟩
  have hold:oldMap ⟨c,q⟩=quotientMap 3 (representative 3 c•tau) := by
    change ((ActualThreeCuspHomeomorph318.cuspHomeomorph (representative 3 c)).symm q).val=_
    rw [show q=ActualThreeCuspHomeomorph318.cuspHomeomorph (representative 3 c)
      (RotatedProjection318.projection 3 (representative 3 c) ⟨tau,ht2⟩) from
      (ActualThreeCuspHomeomorph318.cuspHomeomorph_projection _ _).symm,
      Homeomorph.symm_apply_apply]
    rfl
  exact (original_oldMap ⟨c,q⟩).symm.trans (congrArg (original) hold)

/-- The entire actual all-cusp attachment is covered by a compact original
core and finitely many images of genuinely closed discs. -/
theorem compact_cover :
    (Set.univ:Set (Filled))=
      original '' FiniteCuspCoverage318.compactCore 3 3 ∪
        ⋃c:End 3,Set.range (closedChart c) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases original_or_cusp z with ⟨b,rfl⟩|⟨c,rfl⟩
    · rcases compact_core_and_distinct_ends 3 3 b with hb|⟨c,hc⟩
      · exact Or.inl ⟨b,hb,rfl⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨c,high_mem_closedChart c b hc⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨c,cusp_mem_closedChart c⟩)
  · exact Set.subset_univ _

/-- Compactness is derived from the actual finite fundamental-domain cover,
not supplied as a compact-source premise. -/
theorem filled_compactSpace : CompactSpace (Filled) := by
  letI:NeZero 3:=⟨by omega⟩
  apply isCompact_univ_iff.mp
  rw [compact_cover]
  exact ((FiniteCuspCoverage318.compactCore_isCompact 3 3).image
    (original_openEmbedding).continuous).union (isCompact_iUnion (closedChart_compact))

end ActualThreeCuspCompact318
