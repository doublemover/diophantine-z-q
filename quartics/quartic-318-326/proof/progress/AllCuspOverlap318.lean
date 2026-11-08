module
public import FiniteCuspEnds318
public import TwoChartGluing318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 RotatedHomeomorph318
open scoped MatrixGroups
namespace AllCuspOverlap318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def width (N:ℕ) (hN:5≤N) (c:End N) : ℝ := wReal N hN (representative N c)
theorem width_pos (N:ℕ) (hN:5≤N) (c:End N) : 0<width N hN c := wReal_pos N hN _

@[expose] def disc (N:ℕ) (hN:5≤N) (c:End N) : Set ℂ := {q | ‖q‖<radius (width N hN c) 2}
abbrev Discs (N:ℕ) (hN:5≤N) := Σc:End N,disc N hN c
abbrev Punctures (N:ℕ) (hN:5≤N) := Σc:End N,punctured (width N hN c) 2

theorem disc_open (N:ℕ) (hN:5≤N) (c:End N) : IsOpen (disc N hN c) :=
  isOpen_lt continuous_norm continuous_const

theorem punctured_open (w A:ℝ) : IsOpen (punctured w A) :=
  isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)

@[expose] def oldMap (N:ℕ) (hN:5≤N) (p:Punctures N hN) : Base (image N) :=
  ((cuspHomeomorph N hN (representative N p.1)).symm p.2).val

theorem oldMap_mem (N:ℕ) (hN:5≤N) (p:Punctures N hN) : oldMap N hN p∈p.1.val := by
  rw [←representative_region]
  exact ((cuspHomeomorph N hN (representative N p.1)).symm p.2).property

theorem oldMap_injective (N:ℕ) (hN:5≤N) : Injective (oldMap N hN) := by
  rintro ⟨c,q⟩ ⟨d,r⟩ he
  have hcd:c=d := by
    by_contra hc
    have hr:=oldMap_mem N hN ⟨d,r⟩
    rw [←he] at hr
    exact Set.disjoint_left.mp (regions_disjoint N c d hc) (oldMap_mem N hN ⟨c,q⟩) hr
  subst d
  have hqr:q=r := (cuspHomeomorph N hN (representative N c)).symm.injective (Subtype.ext he)
  exact congrArg (Sigma.mk c) hqr

theorem oldMap_openEmbedding (N:ℕ) (hN:5≤N) : IsOpenEmbedding (oldMap N hN) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply continuous_sigma
    intro c
    exact continuous_subtype_val.comp (cuspHomeomorph N hN (representative N c)).symm.continuous
  · exact oldMap_injective N hN
  · apply isOpenMap_sigma.mpr
    intro c
    exact (RotatedProjection318.neighborhood_open N (representative N c)).isOpenEmbedding_subtypeVal.isOpenMap.comp
      (cuspHomeomorph N hN (representative N c)).symm.isOpenMap

@[expose] def inclusion (N:ℕ) (hN:5≤N) (c:End N) :
    punctured (width N hN c) 2→disc N hN c := fun q=>⟨q.val,q.property.2⟩

@[expose] def discMap (N:ℕ) (hN:5≤N) : Punctures N hN→Discs N hN :=
  Sigma.map id (inclusion N hN)

theorem inclusion_openEmbedding (N:ℕ) (hN:5≤N) (c:End N) : IsOpenEmbedding (inclusion N hN c) := by
  apply IsOpenEmbedding.inclusion (fun q hq=>hq.2)
  exact (punctured_open _ _).preimage continuous_subtype_val

theorem discMap_openEmbedding (N:ℕ) (hN:5≤N) : IsOpenEmbedding (discMap N hN) :=
  (Topology.isOpenEmbedding_sigmaMap Function.injective_id).mpr (inclusion_openEmbedding N hN)

theorem discMap_range (N:ℕ) (hN:5≤N) :
    Set.range (discMap N hN)={q:Discs N hN | q.2.val≠0} := by
  ext q
  constructor
  · rintro ⟨⟨c,p⟩,rfl⟩
    exact p.property.1
  · intro hq
    exact ⟨⟨q.1,⟨q.2.val,hq,q.2.property⟩⟩,rfl⟩

instance punctures_nonempty (N:ℕ) (hN:5≤N) : Nonempty (Punctures N hN) := by
  let c:End N:=Classical.choice (ends_nonempty N)
  let tau:high 2:=⟨⟨3*Complex.I,by norm_num⟩,by change (2:ℝ)<(3*Complex.I).im;norm_num⟩
  exact ⟨⟨c,qMap (width N hN c) 2 (width_pos N hN c) tau⟩⟩

/-- Simultaneous genuine overlap for every distinct actual cusp end. -/
@[expose] def overlap (N:ℕ) (hN:5≤N) : OpenPartialHomeomorph (Base (image N)) (Discs N hN) :=
  ((oldMap_openEmbedding N hN).toOpenPartialHomeomorph (oldMap N hN)).symm.trans
    ((discMap_openEmbedding N hN).toOpenPartialHomeomorph (discMap N hN))

theorem overlap_source (N:ℕ) (hN:5≤N) : (overlap N hN).source=Set.range (oldMap N hN) := by
  simp [overlap,OpenPartialHomeomorph.trans_source]

theorem overlap_target (N:ℕ) (hN:5≤N) :
    (overlap N hN).target={q:Discs N hN | q.2.val≠0} := by
  simp [overlap,OpenPartialHomeomorph.trans_target,discMap_range]

theorem overlap_oldMap (N:ℕ) (hN:5≤N) (p:Punctures N hN) :
    overlap N hN (oldMap N hN p)=discMap N hN p := by
  simp only [overlap,OpenPartialHomeomorph.trans_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,IsOpenEmbedding.toOpenPartialHomeomorph_apply]

end AllCuspOverlap318
