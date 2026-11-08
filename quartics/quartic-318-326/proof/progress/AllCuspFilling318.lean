module
public import AllCuspOverlap318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 AllCuspOverlap318
namespace AllCuspFilling318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine topological gluing of the actual Gamma1 quotient with one filled
width-disc for every distinct end. -/
abbrev Filled (N:ℕ) (hN:5≤N) := TwoChartGluing318.Space (overlap N hN)

@[expose] def original (N:ℕ) (hN:5≤N) : Base (image N)→Filled N hN :=
  TwoChartGluing318.left (overlap N hN)
@[expose] def discsMap (N:ℕ) (hN:5≤N) : Discs N hN→Filled N hN :=
  TwoChartGluing318.right (overlap N hN)
@[expose] def cuspChart (N:ℕ) (hN:5≤N) (c:End N) : disc N hN c→Filled N hN :=
  fun q=>discsMap N hN ⟨c,q⟩
@[expose] def zeroPoint (N:ℕ) (hN:5≤N) (c:End N) : disc N hN c :=
  ⟨0,by change ‖(0:ℂ)‖<radius _ _;simpa using radius_positive (width N hN c) 2⟩
@[expose] def cusp (N:ℕ) (hN:5≤N) (c:End N) : Filled N hN := cuspChart N hN c (zeroPoint N hN c)

theorem original_openEmbedding (N:ℕ) (hN:5≤N) : IsOpenEmbedding (original N hN) :=
  TwoChartGluing318.left_isOpenEmbedding _
theorem discsMap_openEmbedding (N:ℕ) (hN:5≤N) : IsOpenEmbedding (discsMap N hN) :=
  TwoChartGluing318.right_isOpenEmbedding _
theorem cuspChart_openEmbedding (N:ℕ) (hN:5≤N) (c:End N) : IsOpenEmbedding (cuspChart N hN c) :=
  (discsMap_openEmbedding N hN).comp IsOpenEmbedding.sigmaMk

theorem cusp_injective (N:ℕ) (hN:5≤N) : Injective (cusp N hN) := by
  intro c d he
  exact congrArg Sigma.fst ((discsMap_openEmbedding N hN).injective he)

theorem original_ne_cusp (N:ℕ) (hN:5≤N) (b:Base (image N)) (c:End N) :
    original N hN b≠cusp N hN c := by
  intro he
  obtain ⟨hb,hq⟩:=(TwoChartGluing318.left_eq_right_iff (overlap N hN) b ⟨c,zeroPoint N hN c⟩).mp he
  have ht:=(overlap N hN).map_source hb
  rw [hq,overlap_target] at ht
  exact ht rfl

theorem original_oldMap (N:ℕ) (hN:5≤N) (p:Punctures N hN) :
    original N hN (oldMap N hN p)=discsMap N hN (discMap N hN p) := by
  apply (TwoChartGluing318.left_eq_right_iff _ _ _).mpr
  exact ⟨by rw [overlap_source];exact ⟨p,rfl⟩,overlap_oldMap N hN p⟩

/-- Exactly one point is attached for each distinct actual cusp end. -/
theorem original_or_cusp (N:ℕ) (hN:5≤N) (z:Filled N hN) :
    (∃b,original N hN b=z) ∨ ∃c:End N,cusp N hN c=z := by
  rcases TwoChartGluing318.jointly_surjective (overlap N hN) z with ⟨b,hb⟩|⟨⟨c,q⟩,rfl⟩
  · exact Or.inl ⟨b,hb⟩
  · by_cases hq:q.val=0
    · exact Or.inr ⟨c,congrArg (cuspChart N hN c) (Subtype.ext hq.symm)⟩
    · exact Or.inl ⟨oldMap N hN ⟨c,⟨q.val,hq,q.property⟩⟩,original_oldMap N hN _⟩

theorem range_original (N:ℕ) (hN:5≤N) :
    Set.range (original N hN)=(Set.range (cusp N hN))ᶜ := by
  ext z
  constructor
  · rintro ⟨b,rfl⟩ ⟨c,hc⟩
    exact original_ne_cusp N hN b c hc.symm
  · intro hz
    rcases original_or_cusp N hN z with hb|hc
    · exact hb
    · exact False.elim (hz hc)

/-- The finite cusp charts themselves have disjoint ranges. -/
theorem cuspCharts_disjoint (N:ℕ) (hN:5≤N) (c d:End N) (hcd:c≠d) :
    Disjoint (Set.range (cuspChart N hN c)) (Set.range (cuspChart N hN d)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨q,rfl⟩ ⟨r,he⟩
  have hdc:d=c:=congrArg Sigma.fst ((discsMap_openEmbedding N hN).injective he)
  exact hcd hdc.symm

theorem filled_secondCountable (N:ℕ) (hN:5≤N) : SecondCountableTopology (Filled N hN) := by
  letI:NeZero N:=⟨by omega⟩
  letI:SecondCountableTopology (Base (image N)):=ContinuousConstSMul.secondCountableTopology
  let f:Base (image N) ⊕ Discs N hN→Filled N hN:=Sum.elim (original N hN) (discsMap N hN)
  have hc:Continuous f:=continuous_sum_dom.mpr
    ⟨(original_openEmbedding N hN).continuous,(discsMap_openEmbedding N hN).continuous⟩
  have ho:IsOpenMap f:=(original_openEmbedding N hN).isOpenMap.sumElim
    (discsMap_openEmbedding N hN).isOpenMap
  have hs:Surjective f:=by
    intro z
    rcases TwoChartGluing318.jointly_surjective (overlap N hN) z with ⟨b,hb⟩|⟨q,hq⟩
    · exact ⟨Sum.inl b,hb⟩
    · exact ⟨Sum.inr q,hq⟩
  exact (show IsOpenQuotientMap f from ⟨hs,hc,ho⟩).secondCountableTopology

end AllCuspFilling318
