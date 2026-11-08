module
public import FifthFormChartRoute318
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

@[expose] def affine_restrict (i:Fin 4) :=
  IntrinsicChartNaturality318.section_restrict_to
    (ContactUnbranchedDifferentialFrame318.toOpen units) (SourceGlobalAffine318.chartEmbedding units)
    (ContactIntrinsicDifferentials318.structureMap units) (SourceGlobalAffine318.chartEmbedding_over_Q units)
    (embedding units) (over_Q units) (ContactOverlapMaps318.source_square units) sourceLE
    (ContactCharacterAffinePullback318.finiteForm i)
end FifthFormCommonOpen318
