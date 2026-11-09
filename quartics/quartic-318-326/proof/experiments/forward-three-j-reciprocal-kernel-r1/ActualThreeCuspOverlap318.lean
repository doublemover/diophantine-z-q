module
public import FiniteCuspEnds318
public import ActualThreeCuspHomeomorph318
public import ActualThreeCuspExhaustion318
public import TwoChartGluing318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 ActualThreeCuspHomeomorph318
open scoped MatrixGroups
namespace ActualThreeCuspOverlap318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def width (c:End 3) : ℝ := wReal (representative 3 c)
theorem width_pos (c:End 3) : 0<width c := wReal_pos _

@[expose] def disc (c:End 3) : Set ℂ := {q | ‖q‖<radius (width c) 2}
abbrev Discs := Σc:End 3,disc c
abbrev Punctures := Σc:End 3,punctured (width c) 2

theorem disc_open (c:End 3) : IsOpen (disc c) :=
  isOpen_lt continuous_norm continuous_const

theorem punctured_open (w A:ℝ) : IsOpen (punctured w A) :=
  isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)

@[expose] def oldMap (p:Punctures) : Base (image 3) :=
  ((cuspHomeomorph (representative 3 p.1)).symm p.2).val

theorem oldMap_mem (p:Punctures) : oldMap p∈p.1.val := by
  rw [←representative_region]
  exact ((cuspHomeomorph (representative 3 p.1)).symm p.2).property

theorem oldMap_injective : Injective (oldMap) := by
  rintro ⟨c,q⟩ ⟨d,r⟩ he
  have hcd:c=d := by
    by_contra hc
    have hr:=oldMap_mem ⟨d,r⟩
    rw [←he] at hr
    exact Set.disjoint_left.mp (regions_disjoint 3 c d hc) (oldMap_mem ⟨c,q⟩) hr
  subst d
  have hqr:q=r := (cuspHomeomorph (representative 3 c)).symm.injective (Subtype.ext he)
  exact congrArg (Sigma.mk c) hqr

theorem oldMap_openEmbedding : IsOpenEmbedding (oldMap) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply continuous_sigma
    intro c
    exact continuous_subtype_val.comp (cuspHomeomorph (representative 3 c)).symm.continuous
  · exact oldMap_injective
  · apply isOpenMap_sigma.mpr
    intro c
    exact (RotatedProjection318.neighborhood_open 3 (representative 3 c)).isOpenEmbedding_subtypeVal.isOpenMap.comp
      (cuspHomeomorph (representative 3 c)).symm.isOpenMap

@[expose] def inclusion (c:End 3) :
    punctured (width c) 2→disc c := fun q=>⟨q.val,q.property.2⟩

@[expose] def discMap : Punctures→Discs :=
  Sigma.map id (inclusion)

theorem inclusion_openEmbedding (c:End 3) : IsOpenEmbedding (inclusion c) := by
  apply IsOpenEmbedding.inclusion (fun q hq=>hq.2)
  exact (punctured_open _ _).preimage continuous_subtype_val

theorem discMap_openEmbedding : IsOpenEmbedding (discMap) :=
  (Topology.isOpenEmbedding_sigmaMap Function.injective_id).mpr (inclusion_openEmbedding)

theorem discMap_range :
    Set.range (discMap)={q:Discs | q.2.val≠0} := by
  ext q
  constructor
  · rintro ⟨⟨c,p⟩,rfl⟩
    exact p.property.1
  · intro hq
    exact ⟨⟨q.1,⟨q.2.val,hq,q.2.property⟩⟩,rfl⟩

instance punctures_nonempty : Nonempty (Punctures) := by
  let c:End 3:=Classical.choice (ends_nonempty 3)
  let tau:high 2:=⟨⟨3*Complex.I,by norm_num⟩,by change (2:ℝ)<(3*Complex.I).im;norm_num⟩
  exact ⟨⟨c,qMap (width c) 2 (width_pos c) tau⟩⟩

/-- Simultaneous genuine overlap for every distinct actual cusp end. -/
@[expose] def overlap : OpenPartialHomeomorph (Base (image 3)) (Discs) :=
  ((oldMap_openEmbedding).toOpenPartialHomeomorph (oldMap)).symm.trans
    ((discMap_openEmbedding).toOpenPartialHomeomorph (discMap))

theorem overlap_source : (overlap).source=Set.range (oldMap) := by
  simp [overlap,OpenPartialHomeomorph.trans_source]

theorem overlap_target :
    (overlap).target={q:Discs | q.2.val≠0} := by
  simp [overlap,OpenPartialHomeomorph.trans_target,discMap_range]

theorem overlap_oldMap (p:Punctures) :
    overlap (oldMap p)=discMap p := by
  simp only [overlap,OpenPartialHomeomorph.trans_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,IsOpenEmbedding.toOpenPartialHomeomorph_apply]

end ActualThreeCuspOverlap318
