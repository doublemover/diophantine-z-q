module
public import NormalOverlapReciprocalDualSheaf318
public section
noncomputable section
namespace NormalOverlapDifferentialDualTransition318
open IntegralDistinctContactOpen318 IntegralOriginalNormalOverlap318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] (a d : Fin 4 → R)
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "A" => FiniteOverlap R a d
local notation "C" => InfinityOverlap R a d
local notation "E" => overlapEquiv R a d
local notation "τ" => LaurentCoordinateInversion318.tau R
local notation "x" => LaurentCoordinateInversion318.coordinate R
local instance : Algebra S A := (IntegralClosureAlongRingMap318.scalar (finiteMap R a d)).toAlgebra
local instance : Algebra S C := (IntegralClosureAlongRingMap318.scalar (infinityMap R a d)).toAlgebra

@[expose] def finiteFactor : Aˣ := -(Units.map (algebraMap S A).toMonoidHom x)^2
@[expose] def infinityFactor : Cˣ := Units.map E.toMonoidHom (finiteFactor R a d)

lemma finite_factor_scalar : (finiteFactor R a d:A)=algebraMap S A (-(x:S)^2) := by
  change -(algebraMap S A (x:S))^2=_
  rw [map_neg,map_pow]

/-- This is the differential factor -t² in the SAME ambient source,
not the degree-four denominator scaling of the infinity trace lattice. -/
lemma factor_ambient :
    (infinityFactor R a d:C).val=-(IntegralNormalReciprocalForms318.coordinateUnit R a d:
      OpenOrder R a d)^2 := by
  change -(finiteMap R a d (x:S))^2=_
  rw [finite_coordinate]

/-- Multiplication by the actual unit, on the entire OLD infinity dual. -/
@[expose] def scale :
    FiniteDualModuleAction318.Dual S C ≃ₗ[C] FiniteDualModuleAction318.Dual S C where
  toFun f := (infinityFactor R a d:C) • f
  invFun f := (↑(infinityFactor R a d)⁻¹:C) • f
  left_inv f := by rw [←smul_smul,Units.inv_mul,one_smul]
  right_inv f := by rw [←smul_smul,Units.mul_inv,one_smul]
  map_add' f g := smul_add _ _ _
  map_smul' c f := smul_comm _ _ _

@[expose] def moduleIso :=
  NormalOverlapReciprocalDual318.moduleIso R a d ≪≫ (scale R a d).toModuleIso

@[expose] def sheafIso :
    (Scheme.Modules.pullback (NormalOverlapReciprocalDualSheaf318.map R a d)).obj
      (IntegralNormalFiniteDualSheafRestriction318.overlapDual R a d) ≅
        IntegralNormalInfinityDualSheafRestriction318.overlapDual R a d :=
  NormalOverlapReciprocalDualSheaf318.iso R a d ≪≫
    (tilde.functor (CommRingCat.of C)).mapIso (scale R a d).toModuleIso

open scoped TensorProduct in
lemma value (f : FiniteDualModuleAction318.Dual S A) (z : A) :
    (moduleIso R a d).hom (1 ⊗ₜ[A,E.toRingHom] f) (E z)=
      τ (f ((finiteFactor R a d:A)*z)) := by
  change (NormalOverlapReciprocalDual318.moduleIso R a d).hom
    (1 ⊗ₜ[A,E.toRingHom] f) ((infinityFactor R a d:C)*E z)=_
  change (NormalOverlapReciprocalDual318.moduleIso R a d).hom
    (1 ⊗ₜ[A,E.toRingHom] f) (E (finiteFactor R a d:A)*E z)=_
  rw [←map_mul,NormalOverlapReciprocalDual318.one_value]

open scoped TensorProduct in
lemma reciprocal_value (f : FiniteDualModuleAction318.Dual S A) (z : A) :
    (moduleIso R a d).hom (1 ⊗ₜ[A,E.toRingHom] f) (E z)=
      -(↑x⁻¹:S)^2*τ (f z) := by
  rw [value,finite_factor_scalar]
  change τ (f ((-(x:S)^2) • z))=_
  rw [map_smul]
  change τ (-(x:S)^2*f z)=_
  rw [map_mul,map_neg,map_pow,LaurentCoordinateInversion318.coordinate_inverse]
end NormalOverlapDifferentialDualTransition318
