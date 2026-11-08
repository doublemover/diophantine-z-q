module
public import AffineGlobalValueNaturality318
public import ContactGlobalCoefficientScalars318
public import FifthDifferentialTraceComparison318
public section
noncomputable section
namespace ContactGlobalFunctionCoefficient318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCompletedFunctionField318
open ContactGlobalDifferentialCoefficient318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance infinityDomain:IsDomain Infinity:=InfinityOpenChart318.openOrder_domain units
local instance originalAlgebra:Algebra Infinity Raw:=(InfinityOpenFractionField318.openEmbedding units).toAlgebra
attribute [local instance] sourceAlgebra
local instance top_nonempty:Nonempty (⊤:Model.Opens):=⟨⟨genericPoint Model,trivial⟩⟩
local instance infinityMap_open:IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.infinityMap units).toRingHom)):=
  ContactOverlapMaps318.infinityInclusion_open units
abbrev j:=ContactOverlapIntrinsic318.embedding units
abbrev p:=ContactIntrinsicDifferentials318.structureMap units
abbrev M:=ContactIntrinsicDifferentials318.omega units
abbrev O:=ContactKummerOrder318.OpenOrder units
lemma value_infinity (r:Γ(Model,⊤)):
    AffineGlobalFunction318.value j r=ContactOverlapAlgebraMaps318.infinityMap units
      (AffineGlobalFunction318.value (InfinityGlobalScheme318.chartEmbedding units) r):=by
  have h:Spec.map (CommRingCat.ofHom (ContactOverlapAlgebraMaps318.infinityMap units).toRingHom)≫
      InfinityGlobalScheme318.chartEmbedding units=j:=ContactOverlapMaps318.infinity_square units
  exact (AffineGlobalValueNaturality318.value_congr h.symm r).trans
    (AffineGlobalValueNaturality318.value_comp _ _ r)
/-- The value of every actual global regular function in the original
full field agrees with the actual generic stalk, through the same specified
infinity and entire-common-open embeddings. -/
theorem raw_germ (r:Γ(Model,⊤)):
    sourceEquiv (Model.germToFunctionField ⊤ r)=
      SourceOpenFractionField318.openEmbedding units (AffineGlobalFunction318.value j r):=by
  rw [←AffineGlobalFunction318.generic_value (InfinityGlobalScheme318.chartEmbedding units) r,
    source_on_order,value_infinity]
  exact (InfinityOverlapLocalization318.toOpen_embedding units _).symm
lemma form_smul (r:Γ(Model,⊤)) (s:Γ(M,⊤)):
    form (r • s)=AffineGlobalFunction318.value j r • form s:=by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective j p
    (ContactOverlapIntrinsic318.over_Q units)).injective
  rw [form_restrict,Scheme.Modules.map_smul,IntrinsicChartSections318.section_smul]
  change _=ScaledGlobalSectionRestriction318.scalar j (AffineGlobalFunction318.value j r) •
    IntrinsicChartSections318.sectionMap j p (ContactOverlapIntrinsic318.over_Q units) (form s)
  rw [AffineGlobalFunction318.scalar_value,form_restrict]
/-- Scalar compatibility for all global regular functions, not just Q constants. -/
theorem coefficient_smul (r:Γ(Model,⊤)) (s:Γ(M,⊤)):
    coefficient (r • s)=sourceEquiv (Model.germToFunctionField ⊤ r)*coefficient s:=by
  rw [coefficient_apply,form_smul,map_smul,smul_eq_mul,map_mul,raw_germ]
  rfl
theorem genericCoefficient_smul (r:Γ(Model,⊤)) (s:Γ(M,⊤)):
    FifthDifferentialTraceComparison318.genericCoefficient (r • s)=
      Model.germToFunctionField ⊤ r*FifthDifferentialTraceComparison318.genericCoefficient s:=by
  apply sourceEquiv.injective
  rw [FifthDifferentialTraceComparison318.genericCoefficient_raw,map_mul,
    FifthDifferentialTraceComparison318.genericCoefficient_raw,coefficient_smul]
end ContactGlobalFunctionCoefficient318
