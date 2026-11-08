module
public import FifthFormCommonOpen318
public import ContactInfinityTensorRestrictions318
public section
noncomputable section
namespace FifthFormLocalSections318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalCoefficients318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev M:=ContactIntrinsicDifferentials318.omega units

/-- A regular fifth differential on each entire finite branch chart. The
chosen reciprocal root is a proved unit there, not a generic rational function. -/
@[expose] def branch (j:Fin 4):Γ(M,ContactIntrinsicFrames318.branchEmbedding units j ''ᵁ ⊤):=
  ScaledGlobalSectionRestriction318.scaled M (ContactIntrinsicFrames318.branchEmbedding units j)
    (branchCoefficient j) (ContactCharacterDifferentials318.differential (chosen j))

/-- The regular infinity expression uses u/c0, which extends the reciprocal
of the original y0 even at infinity. No division by u occurs here. -/
@[expose] def infinity:Γ(M,InfinityGlobalScheme318.chartEmbedding units ''ᵁ ⊤):=
  ScaledGlobalSectionRestriction318.scaled M (InfinityGlobalScheme318.chartEmbedding units)
    infinityCoefficient (ContactCharacterDifferentials318.differential 0)

local instance branchMap_open (j:Fin 4):IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.branchMap units j).toRingHom)):=
  BranchFullOverlap318.branchInclusion_open units j
local instance infinityMap_open:IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.infinityMap units).toRingHom)):=
  ContactOverlapMaps318.infinityInclusion_open units

theorem branch_restrict (j:Fin 4):
    M.presheaf.map (homOfLE (ContactFiniteTensorRestrictions318.branchLE units j)).op
      (branch j)=FifthFormCommonOpen318.branch j:=
  ScaledGlobalSectionRestriction318.restrict_to M (ContactIntrinsicFrames318.branchEmbedding units j)
    (ContactOverlapAlgebraMaps318.branchMap units j).toRingHom
    (ContactOverlapIntrinsic318.embedding units) (BranchFullOverlap318.branch_square units j)
    (ContactFiniteTensorRestrictions318.branchLE units j) (branchCoefficient j)
      (ContactCharacterDifferentials318.differential (chosen j))

theorem infinity_restrict:
    M.presheaf.map (homOfLE (ContactInfinityTensorRestrictions318.infinityLE units)).op
      infinity=FifthFormCommonOpen318.infinity:=
  ScaledGlobalSectionRestriction318.restrict_to M (InfinityGlobalScheme318.chartEmbedding units)
    (ContactOverlapAlgebraMaps318.infinityMap units).toRingHom
    (ContactOverlapIntrinsic318.embedding units) (ContactOverlapMaps318.infinity_square units)
    (ContactInfinityTensorRestrictions318.infinityLE units) infinityCoefficient
      (ContactCharacterDifferentials318.differential 0)
end FifthFormLocalSections318
