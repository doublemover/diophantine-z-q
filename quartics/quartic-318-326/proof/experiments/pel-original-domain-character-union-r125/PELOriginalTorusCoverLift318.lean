module
public import ComplexTorusCoverHolomorphicLift318
public import PELOriginalCharacterTorus318
public import PELOriginalInvolutionComplexAtlas318
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace PELOriginalTorusCoverLift318
open Set Topology
open scoped Manifold ContDiff
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTorus318
open ComplexLineLatticeAtlas318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (InvolutionBase i):=
  PELOriginalInvolutionComplexAtlas318.involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i):=
  PELOriginalInvolutionComplexAtlas318.involution_manifold i
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (Quotient (periods i)):=chartedSpace (periods i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Quotient (periods i)):=complex_manifold (periods i)

/-- Full path-connectedness is inherited from the SAME original upper
half-plane through the two genuine quotient maps. No connected component
of the original involution quotient is silently discarded. -/
theorem original_pathConnected : PathConnectedSpace (InvolutionBase i) := by
  letI : ContractibleSpace (LegendreHalfPlaneAnalyticSheets318.domain true):=
    (LegendreHalfPlaneAnalyticSheets318.domain_convex true).contractibleSpace
      (LegendreHalfPlaneAnalyticSheets318.domain_nonempty true)
  letI : PathConnectedSpace QuaternionicJointPeriodTopology318.HalfPlane:=by
    change PathConnectedSpace (LegendreHalfPlaneAnalyticSheets318.domain true)
    infer_instance
  infer_instance

lemma original_covering : IsCoveringMap (toCharacterBase i) := by
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  apply IsLocalHomeomorphOn.mk
  intro x _
  obtain ⟨e,hx,he⟩:=local_cover i x
  exact ⟨e,hx,fun y hy=>(he y hy).symm⟩

/-- The actual residual four-cover with its ACTUAL target torus now
constructed, not supplied as a hypothetical genus-one uniformization. -/
@[expose] def torusMap : InvolutionBase i→Quotient (periods i):=
  (comparison i).symm ∘ toCharacterBase i
lemma torusMap_covering : IsCoveringMap (torusMap i):=
  (original_covering i).homeomorph_comp (comparison i).symm
lemma torusMap_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (torusMap i):=
  (biholomorphic i).2.comp (PELOriginalInvolutionComplexAtlas318.toCharacterBase_holomorphic i)
lemma torusMap_surjective : Function.Surjective (torusMap i):=
  (comparison i).symm.surjective.comp (toCharacterBase_surjective i)

@[expose] def origin : InvolutionBase i:=(torusMap_surjective i 0).choose
lemma origin_over_zero : torusMap i (origin i)=projection (periods i) 0:=
  (torusMap_surjective i 0).choose_spec
@[expose] def universalLift : C(ℂ,InvolutionBase i):=
  ComplexTorusCoverLift318.lift (periods i) (torusMap i) (torusMap_covering i)
    (origin i) (origin_over_zero i)
lemma universalLift_origin : universalLift i 0=origin i:=
  ComplexTorusCoverLift318.lift_zero _ _ _ _ _
lemma universalLift_projection (z:ℂ) : torusMap i (universalLift i z)=projection (periods i) z:=
  ComplexTorusCoverLift318.lift_projection _ _ _ _ _ z
lemma universalLift_original_projection (z:ℂ) :
    toCharacterBase i (universalLift i z)=comparison i (projection (periods i) z) := by
  have h:=congrArg (comparison i) (universalLift_projection i z)
  simpa only [torusMap,Function.comp_apply,Homeomorph.apply_symm_apply] using h
lemma universalLift_surjective : Function.Surjective (universalLift i) := by
  letI:=original_pathConnected i
  exact ComplexTorusCoverLift318.lift_surjective _ _ _ _ _
lemma universalLift_localHomeomorph : IsLocalHomeomorph (universalLift i):=
  ComplexTorusCoverLift318.lift_localHomeomorph _ _ _ _ _
lemma universalLift_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (universalLift i):=
  ComplexTorusCoverHolomorphicLift318.lift_holomorphic _ _ _ _ _ (torusMap_holomorphic i)

/-- The fiber count remains the actual everywhere-four count of the
original intermediate quotient, after the actual target homeomorphism. -/
lemma torusMap_fiber_four (q:Quotient (periods i)) :
    Nat.card {x:InvolutionBase i // torusMap i x=q}=4 := by
  let e:{x:InvolutionBase i // torusMap i x=q}≃
      {x:InvolutionBase i // toCharacterBase i x=comparison i q}:={
    toFun x:=⟨x.val,by
      have h:=congrArg (comparison i) x.property
      simpa only [torusMap,Function.comp_apply,Homeomorph.apply_symm_apply] using h⟩
    invFun x:=⟨x.val,by
      change (comparison i).symm (toCharacterBase i x.val)=q
      rw [x.property,Homeomorph.symm_apply_apply]⟩
    left_inv _:=rfl
    right_inv _:=rfl }
  exact (Nat.card_congr e).trans (PELOriginalInvolutionFiber318.every_fiber_four i (comparison i q))
end PELOriginalTorusCoverLift318
