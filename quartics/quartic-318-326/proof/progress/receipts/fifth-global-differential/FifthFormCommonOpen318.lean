module
public import FifthFormWeightedSection318
public section
noncomputable section
namespace FifthFormCommonOpen318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalCoefficients318 ContactOverlapIntrinsic318
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] toOpen_open
/-- Equality of these actual whole-open sections is detected through the
literal etale dt frame and the original injective field embedding. -/
theorem weighted_eq_of_raw (i j:Fin 4) (a b:O)
    (h:SourceOpenFractionField318.openEmbedding units a*
      ContactCharacterFrameValues318.rawValue (ContactCharacterAffinePullback318.finiteForm i)=
        SourceOpenFractionField318.openEmbedding units b*
          ContactCharacterFrameValues318.rawValue (ContactCharacterAffinePullback318.finiteForm j)):
    weighted i a=weighted j b:=by
  rw [weighted_eq_section,weighted_eq_section]
  apply congrArg (IntrinsicChartSections318.sectionMap (embedding units)
    (ContactIntrinsicDifferentials318.structureMap units) (over_Q units))
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  apply SourceOpenFractionField318.openEmbedding_injective units
  simpa only [map_smul,smul_eq_mul,map_mul,ContactCharacterFrameValues318.rawValue,
    ContactCharacterFrameValues318.openValue,form] using h

@[expose] def branch (j:Fin 4):Γ(M,embedding units ''ᵁ ⊤):=
  weighted (chosen j) (ContactOverlapAlgebraMaps318.branchMap units j (branchCoefficient j))
@[expose] def infinity:Γ(M,embedding units ''ᵁ ⊤):=
  weighted 0 (ContactOverlapAlgebraMaps318.infinityMap units infinityCoefficient)

theorem branch_eq_branch (i j:Fin 4):branch i=branch j:=by
  apply weighted_eq_of_raw
  rw [branch_coefficient_image,branch_coefficient_image,common_coefficient,common_coefficient]

theorem branch_eq_infinity (j:Fin 4):branch j=infinity:=by
  apply weighted_eq_of_raw
  rw [branch_coefficient_image,infinity_coefficient_image,common_coefficient,common_coefficient]
end FifthFormCommonOpen318
