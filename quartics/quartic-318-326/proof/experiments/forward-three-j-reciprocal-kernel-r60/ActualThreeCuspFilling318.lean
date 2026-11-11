module
public import ActualThreeCuspOverlap318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 ActualThreeCuspOverlap318
namespace ActualThreeCuspFilling318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine topological gluing of the actual Gamma1 quotient with one filled
width-disc for every distinct end. -/
abbrev Filled := TwoChartGluing318.Space (overlap)

@[expose] def original : Base (image 3)→Filled :=
  TwoChartGluing318.left (overlap)
@[expose] def discsMap : Discs→Filled :=
  TwoChartGluing318.right (overlap)
@[expose] def cuspChart (c:End 3) : disc c→Filled :=
  fun q=>discsMap ⟨c,q⟩
@[expose] def zeroPoint (c:End 3) : disc c :=
  ⟨0,by change ‖(0:ℂ)‖<radius _ _;simpa using radius_positive (width c) 2⟩
@[expose] def cusp (c:End 3) : Filled := cuspChart c (zeroPoint c)

theorem original_openEmbedding : IsOpenEmbedding (original) :=
  TwoChartGluing318.left_isOpenEmbedding _
theorem discsMap_openEmbedding : IsOpenEmbedding (discsMap) :=
  TwoChartGluing318.right_isOpenEmbedding _
theorem cuspChart_openEmbedding (c:End 3) : IsOpenEmbedding (cuspChart c) :=
  (discsMap_openEmbedding).comp IsOpenEmbedding.sigmaMk

theorem cusp_injective : Injective (cusp) := by
  intro c d he
  exact congrArg Sigma.fst ((discsMap_openEmbedding).injective he)

theorem original_ne_cusp (b:Base (image 3)) (c:End 3) :
    original b≠cusp c := by
  intro he
  obtain ⟨hb,hq⟩:=(TwoChartGluing318.left_eq_right_iff (overlap) b ⟨c,zeroPoint c⟩).mp he
  have ht:=(overlap).map_source hb
  rw [hq,overlap_target] at ht
  exact ht rfl

theorem original_oldMap (p:Punctures) :
    original (oldMap p)=discsMap (discMap p) := by
  apply (TwoChartGluing318.left_eq_right_iff _ _ _).mpr
  exact ⟨by rw [overlap_source];exact ⟨p,rfl⟩,overlap_oldMap p⟩

/-- Exactly one point is attached for each distinct actual cusp end. -/
theorem original_or_cusp (z:Filled) :
    (∃b,original b=z) ∨ ∃c:End 3,cusp c=z := by
  rcases TwoChartGluing318.jointly_surjective (overlap) z with ⟨b,hb⟩|⟨⟨c,q⟩,rfl⟩
  · exact Or.inl ⟨b,hb⟩
  · by_cases hq:q.val=0
    · exact Or.inr ⟨c,congrArg (cuspChart c) (Subtype.ext hq.symm)⟩
    · exact Or.inl ⟨oldMap ⟨c,⟨q.val,hq,q.property⟩⟩,original_oldMap _⟩

theorem range_original :
    Set.range (original)=(Set.range (cusp))ᶜ := by
  ext z
  constructor
  · rintro ⟨b,rfl⟩ ⟨c,hc⟩
    exact original_ne_cusp b c hc.symm
  · intro hz
    rcases original_or_cusp z with hb|hc
    · exact hb
    · exact False.elim (hz hc)

/-- The finite cusp charts themselves have disjoint ranges. -/
theorem cuspCharts_disjoint (c d:End 3) (hcd:c≠d) :
    Disjoint (Set.range (cuspChart c)) (Set.range (cuspChart d)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨q,rfl⟩ ⟨r,he⟩
  have hdc:d=c:=congrArg Sigma.fst ((discsMap_openEmbedding).injective he)
  exact hcd hdc.symm

theorem filled_secondCountable : SecondCountableTopology (Filled) := by
  letI:NeZero 3:=⟨by omega⟩
  letI:SecondCountableTopology (Base (image 3)):=ContinuousConstSMul.secondCountableTopology
  let f:Base (image 3) ⊕ Discs→Filled:=Sum.elim (original) (discsMap)
  have hc:Continuous f:=continuous_sum_dom.mpr
    ⟨(original_openEmbedding).continuous,(discsMap_openEmbedding).continuous⟩
  have ho:IsOpenMap f:=(original_openEmbedding).isOpenMap.sumElim
    (discsMap_openEmbedding).isOpenMap
  have hs:Surjective f:=by
    intro z
    rcases TwoChartGluing318.jointly_surjective (overlap) z with ⟨b,hb⟩|⟨q,hq⟩
    · exact ⟨Sum.inl b,hb⟩
    · exact ⟨Sum.inr q,hq⟩
  exact (show IsOpenQuotientMap f from ⟨hs,hc,ho⟩).secondCountableTopology

end ActualThreeCuspFilling318
