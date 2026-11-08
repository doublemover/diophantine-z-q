module
public import ContactBicanonicalSectionNormalization318
public import IntrinsicTensorChartSections318
public section
noncomputable section
namespace ContactLocalTensorExpressions318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.defProp false
variable (c : Fin 4 → ℚˣ)

/-- Kernel-checked proof alias identifying the actual local q0 section
with its coefficient times the actual coordinate differential squared. -/
@[expose] def q0_branch (i : Fin 4) :=
  IntrinsicTensorChartSections318.framed_square
      (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
      (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactIntrinsicDifferentials318.structureMap c)
      (ContactIntrinsicFrames318.branch_structure c i)
      (ContactIntrinsicFrames318.localFrame c (some i))
      (ContactBicanonicalSheaf318.localFrame c (some i))
      (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
        (ContactFrameNormalization318.sourceCoordinate c i))
      (ContactDerivativeFrameComparison318.localDerivative_branch c i)
      (ContactBicanonicalDerivative318.frame_inverse_one c (some i))
      (ContactBicanonicalCoefficients318.branchQ0 c i)

#check q0_branch

@[expose] def q1_branch (i : Fin 4) :=
  IntrinsicTensorChartSections318.framed_square
      (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
      (ContactIntrinsicFrames318.branchEmbedding c i)
      (ContactIntrinsicDifferentials318.structureMap c)
      (ContactIntrinsicFrames318.branch_structure c i)
      (ContactIntrinsicFrames318.localFrame c (some i))
      (ContactBicanonicalSheaf318.localFrame c (some i))
      (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
        (ContactFrameNormalization318.sourceCoordinate c i))
      (ContactDerivativeFrameComparison318.localDerivative_branch c i)
      (ContactBicanonicalDerivative318.frame_inverse_one c (some i))
      (ContactBicanonicalCoefficients318.branchQ1 c i)

#check q1_branch

@[expose] def q0_infinity :=
  IntrinsicTensorChartSections318.framed_square
      (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
      (InfinityGlobalScheme318.chartEmbedding c)
      (ContactIntrinsicDifferentials318.structureMap c)
      (InfinityStructureSmooth318.chartEmbedding_over_Q c)
      (ContactIntrinsicFrames318.localFrame c none)
      (ContactBicanonicalSheaf318.localFrame c none)
      (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
        (ContactFrameNormalization318.infinityCoordinate c))
      (ContactDerivativeFrameComparison318.localDerivative_infinity c)
      (ContactBicanonicalDerivative318.frame_inverse_one c none)
      (ContactBicanonicalCoefficients318.infinityQ0 c)

#check q0_infinity

@[expose] def q1_infinity :=
  IntrinsicTensorChartSections318.framed_square
      (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
      (InfinityGlobalScheme318.chartEmbedding c)
      (ContactIntrinsicDifferentials318.structureMap c)
      (InfinityStructureSmooth318.chartEmbedding_over_Q c)
      (ContactIntrinsicFrames318.localFrame c none)
      (ContactBicanonicalSheaf318.localFrame c none)
      (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
        (ContactFrameNormalization318.infinityCoordinate c))
      (ContactDerivativeFrameComparison318.localDerivative_infinity c)
      (ContactBicanonicalDerivative318.frame_inverse_one c none)
      (ContactBicanonicalCoefficients318.infinityQ1 c)
#check q1_infinity
end ContactLocalTensorExpressions318
