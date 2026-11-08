module
public import FifthBranchDifferential318
public section
noncomputable section
namespace BranchIntrinsicNaturality318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance branchMap_open (j:Fin 4):IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.branchMap c j).toRingHom)):=
  BranchFullOverlap318.branchInclusion_open c j
/-- Actual entire branch-to-common intrinsic restriction, for an arbitrary
algebraic differential and arbitrary unit twists. The proposition is inferred
to retain exactly the chosen sheaf and chart structures. -/
@[expose] def naturality (j:Fin 4)
    (ω:KaehlerDifferential ℚ (ContactIntrinsicFrames318.BranchRing c j)) :=
  IntrinsicChartNaturality318.section_restrict_to
    (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c j) (T:=ContactKummerOrder318.OpenOrder c)
    (ContactOverlapAlgebraMaps318.branchMap c j) (ContactIntrinsicFrames318.branchEmbedding c j)
    (ContactIntrinsicDifferentials318.structureMap c) (ContactIntrinsicFrames318.branch_structure c j)
    (ContactOverlapIntrinsic318.embedding c) (ContactOverlapIntrinsic318.over_Q c)
    (BranchFullOverlap318.branch_square c j) (ContactFiniteTensorRestrictions318.branchLE c j) ω
end BranchIntrinsicNaturality318
