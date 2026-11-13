module
public import OpenFunctionField318
public section
noncomputable section
namespace ActualOpenFractionField318
open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y:Scheme.{u}} [IsIntegral Y] {R:Type u} [CommRing R] [IsDomain R]
    (j:Spec (CommRingCat.of R)⟶Y) [IsOpenImmersion j]
local instance : Algebra R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
local instance : IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of R)
@[expose] def genericEquiv : Y.functionField≃+*(Spec (CommRingCat.of R)).functionField:=
  OpenFunctionField318.fieldEquiv j
/-- Coefficients are embedded by the inverse of the actual open generic-stalk
map, followed by the actual affine coefficient germ. -/
@[expose,instance_reducible] def sourceAlgebra : Algebra R Y.functionField :=
  ((genericEquiv j).symm.toRingHom.comp
    (algebraMap R (Spec (CommRingCat.of R)).functionField)).toAlgebra
@[expose] def genericAlgEquiv :
    letI:=sourceAlgebra j
    Y.functionField≃ₐ[R](Spec (CommRingCat.of R)).functionField:=by
  letI:=sourceAlgebra j
  exact {genericEquiv j with commutes':=by intro a;exact RingEquiv.apply_symm_apply _ _}
theorem fractionRing :
    letI:=sourceAlgebra j
    IsFractionRing R Y.functionField :=by
  letI:=sourceAlgebra j
  exact IsFractionRing.of_algEquiv (genericAlgEquiv j).symm

variable (K:Type u) [CommRing K] [Algebra R K] [IsFractionRing R K]
/-- Whole function-field identification preserving the specified coefficient
map, not an abstract field isomorphism. -/
@[expose] def equiv :
    letI:=sourceAlgebra j
    Y.functionField≃ₐ[R]K:=by
  letI:=sourceAlgebra j
  letI:=fractionRing j
  exact IsLocalization.algEquiv R⁰ _ _
theorem equiv_coeff (a:R):
    letI:=sourceAlgebra j
    equiv j K (algebraMap R Y.functionField a)=algebraMap R K a:=by
  letI:=sourceAlgebra j
  exact (equiv j K).commutes a

theorem generic_germ (U:Y.Opens) [Nonempty U] [Nonempty (j⁻¹ᵁU)] :
    Y.germToFunctionField U≫(OpenFunctionField318.fieldIso j).hom=
      j.app U≫(Spec (CommRingCat.of R)).germToFunctionField (j⁻¹ᵁU):=
  OpenFunctionField318.fieldIso_germ j U
end ActualOpenFractionField318
