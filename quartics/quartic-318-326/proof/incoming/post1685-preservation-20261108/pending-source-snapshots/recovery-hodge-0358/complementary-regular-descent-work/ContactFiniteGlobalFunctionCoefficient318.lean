module
public import ContactGlobalFunctionCoefficient318
public import CompletedCharacterPullback318
public section
noncomputable section
namespace ContactFiniteGlobalFunctionCoefficient318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CompletedCharacterPullback318
open ContactGlobalDifferentialCoefficient318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance sourceDomain:IsDomain Source:=ContactKummerOrder318.source_domain units
local instance originalAlgebra:Algebra Source Raw:=(ContactKummerOrder318.embedding units).toAlgebra
attribute [local instance] sourceOrderAlgebra
local instance top_nonempty:Nonempty (⊤:Model.Opens):=⟨⟨genericPoint Model,trivial⟩⟩
local instance sourceMap_open:IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen units))):=
  ContactOverlapMaps318.sourceInclusion_open units
abbrev j:=ContactOverlapIntrinsic318.embedding units
abbrev M:=ContactIntrinsicDifferentials318.omega units
lemma value_source (r:Γ(Model,⊤)):
    AffineGlobalFunction318.value j r=SourceOpenFractionField318.orderToOpen units
      (AffineGlobalFunction318.value (SourceGlobalAffine318.chartEmbedding units) r):=by
  have h:Spec.map (CommRingCat.ofHom (SourceOpenFractionField318.orderToOpen units))≫
      SourceGlobalAffine318.chartEmbedding units=j:=ContactOverlapMaps318.source_square units
  exact (AffineGlobalValueNaturality318.value_congr h.symm r).trans
    (AffineGlobalValueNaturality318.value_comp _ _ r)
/-- The original four quotient maps use the actual finite-source generic
stalk identification. This compares it to the same literal common value,
rather than silently replacing it by the fifth infinity-chart equivalence. -/
theorem raw_germ (r:Γ(Model,⊤)):
    sourceEquiv (Model.germToFunctionField ⊤ r)=
      SourceOpenFractionField318.openEmbedding units (AffineGlobalFunction318.value j r):=by
  rw [←AffineGlobalFunction318.generic_value (SourceGlobalAffine318.chartEmbedding units) r,
    sourceEquiv.commutes,value_source]
  exact (SourceOpenFractionField318.openEmbedding_on_order units _).symm
/-- Exact arbitrary global regular scalar compatibility through the original
finite-source generic-stalk identification used by the four actual maps. -/
theorem coefficient_smul (r:Γ(Model,⊤)) (s:Γ(M,⊤)):
    coefficient (r • s)=sourceEquiv (Model.germToFunctionField ⊤ r)*coefficient s:=by
  rw [ContactGlobalFunctionCoefficient318.coefficient_smul,
    ContactGlobalFunctionCoefficient318.raw_germ,raw_germ]
end ContactFiniteGlobalFunctionCoefficient318
