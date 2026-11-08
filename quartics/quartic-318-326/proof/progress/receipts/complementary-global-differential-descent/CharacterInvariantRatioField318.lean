module
public import ContactFiniteGlobalFunctionCoefficient318
public import CharacterDifferentialInvariants318
public import CompletedCharacterDegree318
public import ContactCharacterDifferentialNonzero318
public section
noncomputable section
namespace CharacterInvariantRatioField318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterPullback318
open ContactGlobalDifferentialCoefficient318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField:Field Raw:=(KummerTensorField318.source_raw_field units).toField
local instance modelIntegral:IsIntegral Model:=ContactProjectiveModel318.model_integral units
local instance targetIntegral (i:Fin 4):IsIntegral (CompletedCharacterSchemeMaps318.Target i):=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance originalAlgebra:Algebra Source Raw:=(ContactKummerOrder318.embedding units).toAlgebra
attribute [local instance] sourceOrderAlgebra
local instance targetAlgebra (i:Fin 4):Algebra (CompletedCharacterFunctionField318.Order i) (CompletedCharacterSchemeMaps318.Target i).functionField:=CompletedCharacterFunctionField318.orderAlgebra i
local instance characterAlgebra (i:Fin 4):Algebra (CompletedCharacterFunctionField318.Order i) (CompletedCharacterFunctionField318.Character i):=(PublishedCharacterFraction318.embedding i).toAlgebra
local instance modelTop:Nonempty (⊤:Model.Opens):=⟨⟨genericPoint Model,trivial⟩⟩
abbrev M:=ContactIntrinsicDifferentials318.omega units
lemma coefficient_ne_zero (i:Fin 4):coefficient (ContactCharacterDifferentials318.differential i)≠0:=by
  intro h
  apply ContactCharacterDifferentialNonzero318.global_ne_zero i
  apply ContactGlobalCoefficientScalars318.coefficient_injective
  exact h.trans (map_zero coefficient).symm
/-- The generic value of an actual regular global ratio belongs to the
specified original character field by invariance of both nonzero coefficients. -/
lemma ratio_mem (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s)
    (r:Γ(Model,⊤)) (hr:s=r • ContactCharacterDifferentials318.differential i):
    sourceEquiv (Model.germToFunctionField ⊤ r)∈SourceCharacterFields318.field units i:=by
  have hs:=CharacterDifferentialInvariants318.coefficient_mem i s h
  have ht:=CharacterDifferentialInvariants318.coefficient_mem i
    (ContactCharacterDifferentials318.differential i) (CharacterDifferentialInvariants318.own_fixed i)
  have he:sourceEquiv (Model.germToFunctionField ⊤ r)=
      coefficient s/coefficient (ContactCharacterDifferentials318.differential i):=by
    rw [hr,ContactFiniteGlobalFunctionCoefficient318.coefficient_smul,
      mul_div_cancel_right₀ _ (coefficient_ne_zero i)]
  rw [he]
  exact (SourceCharacterFields318.field units i).div_mem hs ht
/-- Membership is transported through the actual target/source generic
stalk square of the original completed quotient, not an arbitrary field map. -/
theorem ratio_range (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s)
    (r:Γ(Model,⊤)) (hr:s=r • ContactCharacterDifferentials318.differential i):
    Set.range (pullback i) (Model.germToFunctionField ⊤ r):=by
  let z:SourceCharacterFields318.field units i:=⟨sourceEquiv (Model.germToFunctionField ⊤ r),ratio_mem i s h r hr⟩
  let a:=(CompletedCharacterFunctionField318.characterEquiv i).symm z
  refine ⟨a,?_⟩
  apply sourceEquiv.injective
  have he:=RingHom.congr_fun (actual_field_square i) a
  change sourceEquiv (pullback i a)=
    (CompletedCharacterFunctionField318.characterEquiv i a:Raw) at he
  rw [he]
  exact congrArg Subtype.val ((CompletedCharacterFunctionField318.characterEquiv i).apply_symm_apply z)
end CharacterInvariantRatioField318
