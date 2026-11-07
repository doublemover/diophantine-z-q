module
public import OpenFunctionField318
public import ArithmeticJModel318
public section
noncomputable section
namespace JModelFunctionField318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

local instance : IsOpenImmersion (OpenJProjectiveMap318.coverMap N B).toNormalization :=
  OpenJProjectiveMap318.coverMap_normalization_open N B

local instance : Algebra B (Spec (CommRingCat.of B)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of B)
local instance : IsFractionRing B (Spec (CommRingCat.of B)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of B)

/-- Actual generic stalk isomorphism of the original open cover into the
constructed proper model. -/
@[expose] def genericStalkIso :
    (OpenJProjectiveMap318.coverMap N B).normalization.functionField ≅
      (Spec (CommRingCat.of B)).functionField :=
  OpenFunctionField318.fieldIso (OpenJProjectiveMap318.coverMap N B).toNormalization

@[expose] def genericStalkEquiv :
    (OpenJProjectiveMap318.coverMap N B).normalization.functionField ≃+*
      (Spec (CommRingCat.of B)).functionField :=
  (genericStalkIso N B).commRingCatIsoToRingEquiv

/-- The coefficient map is induced by the actual source stalk map and germ. -/
@[expose, instance_reducible] def sourceAlgebra :
    Algebra B (OpenJProjectiveMap318.coverMap N B).normalization.functionField :=
  ((genericStalkEquiv N B).symm.toRingHom.comp
    (algebraMap B (Spec (CommRingCat.of B)).functionField)).toAlgebra

attribute [local instance] sourceAlgebra

@[expose] def sourceFieldEquiv :
    (OpenJProjectiveMap318.coverMap N B).normalization.functionField ≃ₐ[B]
      (Spec (CommRingCat.of B)).functionField :=
  { genericStalkEquiv N B with
    commutes' := by intro b; exact RingEquiv.apply_symm_apply _ _ }

/-- The actual generic-point stalk is the fraction field of the original
open-cover algebra; no generic-field identification is a premise. -/
theorem functionField_fractionRing :
    IsFractionRing B (OpenJProjectiveMap318.coverMap N B).normalization.functionField :=
  IsFractionRing.of_algEquiv (sourceFieldEquiv N B).symm

@[expose] def fractionEquiv :
    (OpenJProjectiveMap318.coverMap N B).normalization.functionField ≃ₐ[B] FractionRing B := by
  letI:=functionField_fractionRing N B
  exact IsLocalization.algEquiv B⁰ _ _

theorem fractionEquiv_coeff (b:B) :
    fractionEquiv N B (algebraMap B _ b)=algebraMap B (FractionRing B) b :=
  (fractionEquiv N B).commutes b

/-- Compatibility for all actual section germs along the original source. -/
theorem genericStalkIso_germ
    (U:(OpenJProjectiveMap318.coverMap N B).normalization.Opens)
    [Nonempty U] [Nonempty ((OpenJProjectiveMap318.coverMap N B).toNormalization⁻¹ᵁU)] :
    (OpenJProjectiveMap318.coverMap N B).normalization.germToFunctionField U ≫
      (genericStalkIso N B).hom =
      (OpenJProjectiveMap318.coverMap N B).toNormalization.app U ≫
        (Spec (CommRingCat.of B)).germToFunctionField
          ((OpenJProjectiveMap318.coverMap N B).toNormalization⁻¹ᵁU) :=
  OpenFunctionField318.fieldIso_germ _ U
end JModelFunctionField318
