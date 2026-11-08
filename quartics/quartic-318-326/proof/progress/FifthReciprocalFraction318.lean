module
public import FifthReciprocalCoordinates318
public import FractionFieldLocalizationDescent318
public section
noncomputable section
namespace FifthReciprocalFraction318
open Polynomial QuadraticPresentation318 FifthCharacterPolynomial318 FifthCharacterReciprocal318
open FifthReciprocalCoordinates318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev R:=ℚ[X]
abbrev QOrder:=FifthCharacterOrder318.Order
abbrev COrder:=RootRing reciprocal
abbrev Field:=FifthCharacterField318.field
attribute [local instance] Algebra.TensorProduct.rightAlgebra
local instance qDomain:IsDomain QOrder:=FifthCharacterOrder318.embedding_injective.isDomain
local instance qAlgebra:Algebra QOrder Field:=FifthCharacterOrder318.embedding.toAlgebra
local instance qFraction:IsFractionRing QOrder Field:=FifthCharacterOrder318.actual_fractionField
local instance qLocal:IsLocalization.Away (algebraMap R QOrder X) QuarticTensor:=quartic_localization
local instance cLocal:IsLocalization.Away (algebraMap R COrder X) CubicTensor:=cubic_localization

lemma parameter_image_unit : IsUnit (FifthCharacterOrder318.embedding (algebraMap R QOrder X)) := by
  rw [FifthCharacterOrder318.embedding_on_polynomial]
  apply IsUnit.mk0
  apply (_root_.map_ne_zero (algebraMap (RatFunc ℚ) Field)).mpr
  exact (map_ne_zero_iff (algebraMap R (RatFunc ℚ)) (IsFractionRing.injective R (RatFunc ℚ))).mpr Polynomial.X_ne_zero

@[expose] def quarticEmbedding : QuarticTensor→+*Field :=
  IsLocalization.Away.lift (algebraMap R QOrder X) parameter_image_unit
lemma quarticEmbedding_on_order (x:QOrder) :
    quarticEmbedding (algebraMap QOrder QuarticTensor x)=FifthCharacterOrder318.embedding x :=
  IsLocalization.Away.lift_eq _ _ _
local instance qtAlgebra:Algebra QuarticTensor Field:=quarticEmbedding.toAlgebra
local instance qtTower:IsScalarTower QOrder QuarticTensor Field:=
  IsScalarTower.of_algebraMap_eq (fun x=>(quarticEmbedding_on_order x).symm)

theorem quartic_fractionField:IsFractionRing QuarticTensor Field:=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (algebraMap R QOrder X)) QuarticTensor Field

@[expose] def cubicEmbedding : CubicTensor→+*Field :=
  quarticEmbedding.comp tensorEquiv.symm.toRingHom
local instance ctAlgebra:Algebra CubicTensor Field:=cubicEmbedding.toAlgebra

theorem cubic_fractionField:IsFractionRing CubicTensor Field:=by
  letI:=quartic_fractionField
  exact IsFractionRing.of_ringEquiv_left tensorEquiv.symm.toRingEquiv (fun _=>rfl)

theorem cubicEmbedding_injective:Function.Injective cubicEmbedding:=by
  letI:=cubic_fractionField
  exact IsFractionRing.injective CubicTensor Field

@[expose] def embedding:COrder→+*Field:=
  cubicEmbedding.comp (algebraMap COrder CubicTensor)
local instance cAlgebra:Algebra COrder Field:=embedding.toAlgebra
local instance cTower:IsScalarTower COrder CubicTensor Field:=
  IsScalarTower.of_algebraMap_eq (R:=COrder) (S:=CubicTensor) (A:=Field) (fun x=>show embedding x = cubicEmbedding (algebraMap COrder CubicTensor x) from rfl)

theorem embedding_injective:Function.Injective embedding:=by
  letI:Module.Free R COrder:=FourRootOrder318.root_free _
  apply cubicEmbedding_injective.comp
  exact Algebra.TensorProduct.includeRight_injective (R:=R) (A:=Laurent) (B:=COrder)
    Polynomial.toLaurent_injective

/-- The entire reciprocal cubic order has the actual original full-root
character subfield as its fraction field, via the specified reciprocal embedding. -/
theorem actual_fractionField:IsFractionRing COrder Field:=by
  letI:=cubic_fractionField
  letI:FaithfulSMul COrder Field:= (faithfulSMul_iff_algebraMap_injective COrder Field).mpr embedding_injective
  exact FractionFieldLocalizationDescent318.of_localization
    (S:=CubicTensor) (Submonoid.powers (algebraMap R COrder X))
end FifthReciprocalFraction318
