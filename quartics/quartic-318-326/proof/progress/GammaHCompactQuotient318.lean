module
public import GammaHCompactAction318
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open GammaHGroup318 GammaHDiamond318 GammaHAction318 GammaHCuspEnds318 GammaHFilledAction318
open GammaHCompactAction318 FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 AllCuspInfinity318
namespace GammaHCompactQuotient318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

variable (N:ℕ) (hN:5≤N) [NeZero N] (H:Subgroup (ZMod N)ˣ)
local instance : MulAction H (Fine N) := GammaHAction318.diamondAction N H
local instance : MulAction H (End N) := endDiamondAction N H
local instance : MulAction H (Filled N hN) := filledDiamondAction N hN H
local instance : ContinuousConstSMul H (Fine N) := GammaHAction318.diamond_continuous N H
local instance : ContinuousConstSMul H (Filled N hN) := GammaHCompactAction318.diamond_continuous N hN H
local instance : CompactSpace (Filled N hN) := AllCuspCompact318.filled_compactSpace N hN
local instance : T2Space (Filled N hN) := AllCuspHausdorff318.filled_t2 N hN
local instance : SecondCountableTopology (Filled N hN) := filled_secondCountable N hN
local instance : ConnectedSpace (Filled N hN) := AllCuspConnected318.filled_connected N hN

/-- The actual finite diamond quotient of the actual all-cusp filling. -/
abbrev CompactCurve := MulAction.orbitRel.Quotient H (Filled N hN)
@[expose] def projection : Filled N hN→CompactCurve N hN H :=
  Quotient.mk (MulAction.orbitRel H (Filled N hN))

theorem projection_openQuotient : IsOpenQuotientMap (projection N hN H) :=
  MulAction.isOpenQuotientMap_quotientMk

theorem compact_topology : CompactSpace (CompactCurve N hN H) ∧ T2Space (CompactCurve N hN H) ∧
    SecondCountableTopology (CompactCurve N hN H) ∧ ConnectedSpace (CompactCurve N hN H) :=
  ⟨inferInstance,inferInstance,ContinuousConstSMul.secondCountableTopology,inferInstance⟩

@[expose] def originalMap : GammaHDiamondQuotient318.DiamondQuotient N H→CompactCurve N hN H :=
  Quotient.lift (fun b=>projection N hN H (original N hN b)) (by
    intro a b hab
    obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp hab
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨u,?_⟩
    change u•original N hN b=original N hN a
    exact (diamond_original N hN H u b).trans (congrArg (original N hN) hu))

theorem originalMap_apply (b:Fine N) :
    originalMap N hN H (GammaHDiamondQuotient318.quotient N H b)=projection N hN H (original N hN b) := rfl

theorem originalMap_continuous : Continuous (originalMap N hN H) :=
  continuous_quot_lift _ (continuous_quot_mk.comp (original_openEmbedding N hN).continuous)

theorem originalMap_injective : Injective (originalMap N hN H) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h b =>
    induction y using Quotient.inductionOn with
    | h d =>
      obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp (Quotient.exact h)
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      refine ⟨u,?_⟩
      apply (original_openEmbedding N hN).injective
      exact (diamond_original N hN H u d).symm.trans hu

theorem originalMap_open : IsOpenMap (originalMap N hN H) := by
  intro U hU
  let q:=GammaHDiamondQuotient318.quotient N H
  have hq:IsOpenQuotientMap q:=MulAction.isOpenQuotientMap_quotientMk
  have he : originalMap N hN H '' U=projection N hN H '' (original N hN '' (q⁻¹' U)) := by
    ext z
    constructor
    · rintro ⟨b,hb,rfl⟩
      obtain ⟨x,rfl⟩:=hq.surjective b
      exact ⟨original N hN x,⟨x,hb,rfl⟩,rfl⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨q x,hx,rfl⟩
  rw [he]
  exact (projection_openQuotient N hN H).isOpenMap _
    ((original_openEmbedding N hN).isOpenMap _ (hU.preimage hq.continuous))

theorem originalMap_openEmbedding : IsOpenEmbedding (originalMap N hN H) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (originalMap_continuous N hN H)
    (originalMap_injective N hN H) (originalMap_open N hN H)

theorem originalMap_dense : DenseRange (originalMap N hN H) := by
  intro y
  obtain ⟨z,rfl⟩:=(projection_openQuotient N hN H).surjective y
  have hh:=mem_closure_image (projection_openQuotient N hN H).continuous.continuousAt
    (AllCuspHausdorff318.original_dense N hN z)
  apply closure_mono _ hh
  rintro w ⟨_,⟨b,rfl⟩,rfl⟩
  exact ⟨GammaHDiamondQuotient318.quotient N H b,rfl⟩

/-- The compact quotient's cusp labels are the actual orbits of the actual
finite distinct-end permutation. -/
@[expose] def cuspMap : OrbitEnds N H→CompactCurve N hN H :=
  Quotient.lift (fun c=>projection N hN H (cusp N hN c)) (by
    intro c d hcd
    obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp hcd
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨u,?_⟩
    change u•cusp N hN d=cusp N hN c
    exact (diamond_cusp N hN H u d).trans (congrArg (cusp N hN) hu))

theorem cuspMap_injective : Injective (cuspMap N hN H) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h c =>
    induction y using Quotient.inductionOn with
    | h d =>
      obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp (Quotient.exact h)
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      refine ⟨u,?_⟩
      apply cusp_injective N hN
      exact (diamond_cusp N hN H u d).symm.trans hu

theorem originalMap_ne_cuspMap (x:GammaHDiamondQuotient318.DiamondQuotient N H) (c:OrbitEnds N H) :
    originalMap N hN H x≠cuspMap N hN H c := by
  induction x using Quotient.inductionOn with
  | h b =>
    induction c using Quotient.inductionOn with
    | h d =>
      intro he
      obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp (Quotient.exact he)
      exact original_ne_cusp N hN b (u•d) ((diamond_cusp N hN H u d).symm.trans hu).symm

theorem range_originalMap : Set.range (originalMap N hN H)=(Set.range (cuspMap N hN H))ᶜ := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩ ⟨c,hc⟩
    exact originalMap_ne_cuspMap N hN H x c hc.symm
  · intro hy
    obtain ⟨z,rfl⟩:=(projection_openQuotient N hN H).surjective y
    rcases original_or_cusp N hN z with ⟨b,rfl⟩|⟨c,rfl⟩
    · exact ⟨GammaHDiamondQuotient318.quotient N H b,rfl⟩
    · exact False.elim (hy ⟨⟦c⟧,rfl⟩)

/-- The actual compact H quotient, with dense open original quotient and a
finite, distinctly embedded actual cusp-orbit complement. -/
theorem actual_compactification :
    CompactSpace (CompactCurve N hN H) ∧ T2Space (CompactCurve N hN H) ∧
    SecondCountableTopology (CompactCurve N hN H) ∧ ConnectedSpace (CompactCurve N hN H) ∧
    IsOpenEmbedding (originalMap N hN H) ∧ DenseRange (originalMap N hN H) ∧
    Injective (cuspMap N hN H) ∧ Set.range (originalMap N hN H)=(Set.range (cuspMap N hN H))ᶜ := by
  obtain ⟨hc,ht,hs,hconn⟩:=compact_topology N hN H
  exact ⟨hc,ht,hs,hconn,originalMap_openEmbedding N hN H,originalMap_dense N hN H,
    cuspMap_injective N hN H,range_originalMap N hN H⟩

/-- The same genuine sphere-valued j extends continuously on the actual
compact H quotient, and sends exactly the actual cusp orbits to infinity. -/
@[expose] def compactJ : CompactCurve N hN H→OnePoint ℂ :=
  Quotient.lift (jInfinity N hN) (by
    intro a b hab
    obtain ⟨u,hu⟩:=MulAction.orbitRel_apply.mp hab
    rw [←hu]
    exact diamond_jInfinity N hN H u b)

theorem compactJ_continuous : Continuous (compactJ N hN H) :=
  continuous_quot_lift _ (jInfinity_continuous N hN)

theorem compactJ_original (b:Fine N) :
    compactJ N hN H (originalMap N hN H (GammaHDiamondQuotient318.quotient N H b))=
      (QuotientJ318.jMap N b:OnePoint ℂ) := jInfinity_original N hN b

theorem compactJ_cusp (c:OrbitEnds N H) : compactJ N hN H (cuspMap N hN H c)=OnePoint.infty := by
  induction c using Quotient.inductionOn with
  | h c => exact jInfinity_cusp N hN c

end GammaHCompactQuotient318
