module
public import ContactBicanonicalDerivative318
public section
noncomputable section
namespace ContactDerivativeFrameComparison318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

theorem branchFrame_eq (i : Fin 4) :
    ContactIntrinsicFrames318.localFrame c (some i) =
      IntrinsicFrameDerivative318.chartFrame
        (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
        (ContactIntrinsicFrames318.branchEmbedding c i)
        (ContactIntrinsicDifferentials318.structureMap c)
        (ContactIntrinsicFrames318.branch_structure c i)
        (ContactDifferentialFrames318.sourceLocalizationFrame c i) := rfl

theorem infinityFrame_eq :
    ContactIntrinsicFrames318.localFrame c none =
      IntrinsicFrameDerivative318.chartFrame
        (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
        (InfinityGlobalScheme318.chartEmbedding c)
        (ContactIntrinsicDifferentials318.structureMap c)
        (InfinityStructureSmooth318.chartEmbedding_over_Q c)
        (ContactDifferentialFrames318.infinityFrame c) := rfl
-- Inferred proof types preserve the exact concrete chosen module objects.
-- These are kernel-checked proofs; no proposition is introduced as an axiom.
set_option linter.defProp false
/-- The actual branch inverse frame is the universal derivative of z_i. -/
@[expose] def localDerivative_branch (i : Fin 4) :=
  IntrinsicFrameDerivative318.frame_inverse_section_of_eq
    (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing c i)
    (ContactIntrinsicFrames318.branchEmbedding c i)
    (ContactIntrinsicDifferentials318.structureMap c)
    (ContactIntrinsicFrames318.branch_structure c i)
    (ContactDifferentialFrames318.sourceLocalizationFrame c i)
    (ContactIntrinsicFrames318.localFrame c (some i)) (branchFrame_eq c i)
    (ContactFrameNormalization318.sourceCoordinate c i)
    (ContactFrameNormalization318.source_coordinate_normalized c i)

/-- The actual infinity inverse frame is the universal derivative of u=c₀/y₀. -/
@[expose] def localDerivative_infinity :=
  IntrinsicFrameDerivative318.frame_inverse_section_of_eq
    (R:=ℚ) (S:=InfinityGlobalChart318.InfinityOrder c)
    (InfinityGlobalScheme318.chartEmbedding c)
    (ContactIntrinsicDifferentials318.structureMap c)
    (InfinityStructureSmooth318.chartEmbedding_over_Q c)
    (ContactDifferentialFrames318.infinityFrame c)
    (ContactIntrinsicFrames318.localFrame c none) (infinityFrame_eq c)
    (ContactFrameNormalization318.infinityCoordinate c)
    (ContactFrameNormalization318.infinity_coordinate_normalized c)
end ContactDerivativeFrameComparison318
