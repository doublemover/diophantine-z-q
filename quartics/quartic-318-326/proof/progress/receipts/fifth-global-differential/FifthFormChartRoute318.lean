module
public import FifthFormLocalCoefficients318
public import ScaledGlobalSectionRestriction318
public import ContactOverlapIntrinsic318
public section
noncomputable section
namespace FifthFormCommonOpen318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalCoefficients318 ContactOverlapIntrinsic318
set_option maxHeartbeats 150000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev M:=ContactIntrinsicDifferentials318.omega units
local instance toOpen_open:IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (ContactUnbranchedDifferentialFrame318.toOpen units).toRingHom)):=
  ContactOverlapMaps318.sourceInclusion_open units

lemma sourceLE:embedding units ''ᵁ ⊤≤SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤:=by
  have h:=OpenChartSections318.imageLE (ContactOverlapMaps318.sourceInclusion units)
    (SourceGlobalAffine318.chartEmbedding units)
  simpa only [ContactOverlapMaps318.source_square,embedding] using h

@[expose] def form (i:Fin 4):KaehlerDifferential ℚ O:=
  AlgHomDifferential318.map (ContactUnbranchedDifferentialFrame318.toOpen units)
    (ContactCharacterAffinePullback318.finiteForm i)

end FifthFormCommonOpen318
