module
public import FifthQuarticCover318
public import FifthShortFraction318
public import FifthCharacterShortScheme318
public section
noncomputable section
namespace FifthQuarticFinite318
open Polynomial QuadraticPresentation318 FifthCharacterPolynomial318
open FifthCharacterReciprocal318 FifthReciprocalCoordinates318 FifthQuarticCover318
open FifthCharacterShortPolynomial318 FifthCharacterShortAlgebra318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Algebra.TensorProduct.rightAlgebra
abbrev Local:=Localization.Away parameter
local instance qtRatTower:IsScalarTower ℚ Quartic QuarticTensor:=
  IsScalarTower.of_algebraMap_eq (fun q=>by
    rw [IsScalarTower.algebraMap_apply ℚ ℚ[X] Quartic,
      ←IsScalarTower.algebraMap_apply ℚ[X] Quartic QuarticTensor,
      ←IsScalarTower.algebraMap_apply ℚ ℚ[X] QuarticTensor])
local instance qtLocal:IsLocalization.Away parameter QuarticTensor:=quartic_localization
@[expose] def tensorIso:Local≃ₐ[Quartic]QuarticTensor:=
  IsLocalization.algEquiv (Submonoid.powers parameter) Local QuarticTensor
@[expose] def cubicMap:CubicRing→ₐ[ℚ]Local:=
  (tensorIso.symm.restrictScalars ℚ).toAlgHom.comp
    (tensorEquiv.symm.toAlgHom.comp
      ((Algebra.TensorProduct.includeRight : CubicRing→ₐ[ℚ[X]]CubicTensor).restrictScalars ℚ))
@[expose] def shortMap:ShortAffineJacobian318.Ring A B→ₐ[ℚ]Local:=
  cubicMap.comp coordinateEquiv.symm.toAlgHom
@[expose] def fieldEmbedding:Local→+*FifthCharacterField318.field:=
  FifthReciprocalFraction318.quarticEmbedding.comp tensorIso.toRingHom

theorem fieldEmbedding_injective:Function.Injective fieldEmbedding:=by
  letI:Algebra QuarticTensor FifthCharacterField318.field:=FifthReciprocalFraction318.quarticEmbedding.toAlgebra
  letI:=FifthReciprocalFraction318.quartic_fractionField
  exact (IsFractionRing.injective QuarticTensor FifthCharacterField318.field).comp tensorIso.injective
lemma fieldEmbedding_on_order (x:Quartic):
    fieldEmbedding (algebraMap Quartic Local x)=FifthCharacterOrder318.embedding x:=by
  change FifthReciprocalFraction318.quarticEmbedding (tensorIso (algebraMap Quartic Local x))=_
  rw [AlgEquiv.commutes]
  exact FifthReciprocalFraction318.quarticEmbedding_on_order x
lemma cubicMap_field (x:CubicRing):
    fieldEmbedding (cubicMap x)=FifthReciprocalFraction318.embedding x:=by
  change FifthReciprocalFraction318.quarticEmbedding
    (tensorIso (tensorIso.symm (tensorEquiv.symm (1⊗ₜ[ℚ[X]]x))))=_
  rw [AlgEquiv.apply_symm_apply]
  rfl
lemma shortMap_field (x:ShortAffineJacobian318.Ring A B):
    fieldEmbedding (shortMap x)=FifthShortFraction318.embedding x:=
  cubicMap_field _

@[expose] def map:Spec (CommRingCat.of Local)⟶FifthCharacterShortScheme318.completed:=
  Spec.map (CommRingCat.ofHom shortMap.toRingHom)≫WeierstrassGluing318.finiteChart A B
@[reassoc] theorem over_Q:
    map≫WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ Local)):=by
  rw [map,Category.assoc,WeierstrassGluing318.finiteChart_structure]
  change Spec.map (CommRingCat.ofHom shortMap.toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ _))=_
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  exact shortMap.commutes q
end FifthQuarticFinite318
