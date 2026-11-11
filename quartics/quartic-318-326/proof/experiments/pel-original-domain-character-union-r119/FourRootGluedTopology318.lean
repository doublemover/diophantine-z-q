module
public import FourRootNormalizedOverlap318
public section
noncomputable section
namespace FourRootGluedTopology318
open Set Topology FourRootNormalizedPointCharts318 FourRootNormalizedOverlap318
variable (b:Fin 4→ℂ)

/-- Glue the TWO INDEPENDENT affine coordinate spaces. This is explicitly
NOT the disjoint-sum topology on the set-level completed carrier, and is
not transported from the original PEL curve. -/
@[expose] def chartMap : FinitePoints b⊕InfinityPoints b→Completed b:=
  Sum.elim (finiteChart b) (infinityChart b)
@[expose] def topology : TopologicalSpace (Completed b):=
  TopologicalSpace.coinduced (chartMap b) inferInstance
local instance : TopologicalSpace (Completed b):=topology b

lemma isOpen_iff (V:Set (Completed b)) : IsOpen V ↔
    IsOpen (finiteChart b ⁻¹' V) ∧ IsOpen (infinityChart b ⁻¹' V):=Iff.rfl
lemma finiteChart_continuous : Continuous (finiteChart b):=
  ⟨fun V hV=>(isOpen_iff b V).mp hV |>.1⟩
lemma infinityChart_continuous : Continuous (infinityChart b):=
  ⟨fun V hV=>(isOpen_iff b V).mp hV |>.2⟩

lemma cross_finite_image (V:Set (FinitePoints b)) :
    infinityChart b ⁻¹' (finiteChart b '' V)=
      Subtype.val '' ((toFinite b) ⁻¹' (Subtype.val ⁻¹' V)) := by
  ext q
  constructor
  · rintro ⟨p,hp,he⟩
    have hq:q.val.1≠0:=by
      intro hz
      rw [infinityChart,dif_pos hz] at he
      cases he
    refine ⟨⟨q,hq⟩,?_,rfl⟩
    have hh:p=(toFinite b ⟨q,hq⟩).val:=
      Sum.inl.inj (he.trans (infinityChart_nonzero b q hq))
    exact hh ▸ hp
  · rintro ⟨q,hq,rfl⟩
    exact ⟨(toFinite b q).val,hq,(infinityChart_nonzero b q.val q.property).symm⟩

lemma cross_infinity_image (V:Set (InfinityPoints b)) :
    finiteChart b ⁻¹' (infinityChart b '' V)=
      Subtype.val '' ((toInfinity b) ⁻¹' (Subtype.val ⁻¹' V)) := by
  ext p
  constructor
  · rintro ⟨q,hq,he⟩
    have hn:q.val.1≠0:=by
      intro hz
      rw [infinityChart,dif_pos hz] at he
      cases he
    have hh:(toFinite b ⟨q,hn⟩).val=p:=
      Sum.inl.inj ((infinityChart_nonzero b q hn).symm.trans he)
    let po:FiniteOverlap b:=⟨p,hh ▸ (toFinite b ⟨q,hn⟩).property⟩
    have hpo:toFinite b ⟨q,hn⟩=po:=Subtype.ext hh
    refine ⟨po,?_,rfl⟩
    have hback:toInfinity b po=⟨q,hn⟩:=by
      rw [←hpo,toInfinity_toFinite]
    change (toInfinity b po).val∈V
    rw [hback]
    exact hq
  · rintro ⟨p,hp,rfl⟩
    exact ⟨(toInfinity b p).val,hp,overlap_agreement b p⟩

lemma finiteChart_open : IsOpenMap (finiteChart b) := by
  intro V hV
  apply (isOpen_iff b _).mpr
  constructor
  · simpa only [finiteChart,preimage_image_eq V Sum.inl_injective] using hV
  · rw [cross_finite_image]
    have hpre:IsOpen ((toFinite b) ⁻¹' (Subtype.val ⁻¹' V)):=
      (hV.preimage continuous_subtype_val).preimage (toFinite_continuous b)
    exact (infinity_overlap_open b).isOpenEmbedding_subtypeVal.isOpenMap _ hpre

lemma infinityChart_open : IsOpenMap (infinityChart b) := by
  intro V hV
  apply (isOpen_iff b _).mpr
  constructor
  · rw [cross_infinity_image]
    have hpre:IsOpen ((toInfinity b) ⁻¹' (Subtype.val ⁻¹' V)):=
      (hV.preimage continuous_subtype_val).preimage (toInfinity_continuous b)
    exact (finite_overlap_open b).isOpenEmbedding_subtypeVal.isOpenMap _ hpre
  · simpa only [preimage_image_eq V (infinityChart_injective b)] using hV

/-- Both charts are genuine open embeddings for this explicit glued
topology. In particular infinity neighborhoods contain nearby finite
points; they are not isolated as in the accidental disjoint-sum topology. -/
theorem finite_openEmbedding : IsOpenEmbedding (finiteChart b):=
  isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨finiteChart_continuous b,Sum.inl_injective,finiteChart_open b⟩
theorem infinity_openEmbedding : IsOpenEmbedding (infinityChart b):=
  isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨infinityChart_continuous b,infinityChart_injective b,infinityChart_open b⟩

/-- Universal property uses the independent affine charts on BOTH sides
of infinity. This can certify continuity of the completed source map
once actual finite/infinity coordinate extensions have been produced. -/
theorem continuous_iff {X:Type*} [TopologicalSpace X] (f:Completed b→X) :
    Continuous f ↔ Continuous (f ∘ finiteChart b) ∧ Continuous (f ∘ infinityChart b) := by
  change @Continuous (Completed b) X (TopologicalSpace.coinduced (chartMap b) _) _ f ↔ _
  rw [continuous_coinduced_dom,continuous_sum_dom]
  rfl
end FourRootGluedTopology318
