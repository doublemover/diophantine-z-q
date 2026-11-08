module
public import ContactBicanonicalCoefficients318
public import ContactIntrinsicFrames318
public import IntrinsicTensorChartSections318
public section
noncomputable section
namespace ContactDirectTensorSections318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The same genuine intrinsic tensor-square object, with its exact generic
arguments retained for the restriction and gluing proofs. -/
abbrev tensor := IntrinsicTensorSheaf318.tensor
  (FamilyIntrinsicDifferentials318.omega (ContactIntrinsicDifferentials318.structureMap c))
  (FamilyIntrinsicDifferentials318.omega (ContactIntrinsicDifferentials318.structureMap c))

/-- Direct actual intrinsic section, with the verified coefficient and
universal coordinate derivative, rather than a named abstract line generator. -/
@[expose] def branchQ0 (i : Fin 4) :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i) (ContactBicanonicalCoefficients318.branchQ0 c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
@[expose] def branchQ1 (i : Fin 4) :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i) (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i) (ContactBicanonicalCoefficients318.branchQ1 c i)
    (KaehlerDifferential.D ℚ (ContactIntrinsicFrames318.BranchRing c i)
      (ContactFrameNormalization318.sourceCoordinate c i))
@[expose] def infinityQ0 :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) (ContactBicanonicalCoefficients318.infinityQ0 c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
      (ContactFrameNormalization318.infinityCoordinate c))
@[expose] def infinityQ1 :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c) (ContactIntrinsicDifferentials318.structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c) (ContactBicanonicalCoefficients318.infinityQ1 c)
    (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c)
      (ContactFrameNormalization318.infinityCoordinate c))
end ContactDirectTensorSections318
