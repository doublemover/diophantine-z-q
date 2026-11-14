module
public import IntegralSectionProjectiveMap318
public section
noncomputable section
namespace UnitSquarePolynomialFinite318
open Polynomial AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R] (a : Rˣ)
@[expose] def squareCoordinate : R[X] →ₐ[R] R[X] :=
  Polynomial.aeval (C (↑a⁻¹:R)*X^2)

/-- The quadratic coordinate map factors through the actual monic original
root algebra and its explicit coordinate equivalence. -/
theorem factor : (squareCoordinate a).toRingHom=
    (LinearRootCoordinate318.coordinateEquiv a 0).toRingHom.comp
      (algebraMap R[X] (LinearRootCoordinate318.Root a 0)) := by
  apply Polynomial.ringHom_ext
  · intro r
    change squareCoordinate a (C r)=LinearRootCoordinate318.coordinateEquiv a 0
      (algebraMap R[X] (LinearRootCoordinate318.Root a 0) (C r))
    rw [squareCoordinate,Polynomial.aeval_C,LinearRootCoordinate318.coordinate_base]
    simp only [LinearRootCoordinate318.baseSubstitution,Polynomial.aeval_C]
  · change squareCoordinate a X=LinearRootCoordinate318.coordinateEquiv a 0
      (algebraMap R[X] (LinearRootCoordinate318.Root a 0) X)
    rw [squareCoordinate,Polynomial.aeval_X]
    exact (by simpa only [Polynomial.C_0,sub_zero] using
      LinearRootCoordinate318.coordinate_contact a (0:R)).symm

/-- The actual scaled-square map of affine lines is finite over any base;
no field-only polynomial-degree argument is substituted. -/
instance finite : IsFinite (Spec.map (CommRingCat.ofHom (squareCoordinate a).toRingHom)) := by
  letI : Module.Finite R[X] (LinearRootCoordinate318.Root a 0) :=
    FourRootOrder318.root_finite (LinearRootCoordinate318.parameter a 0)
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R[X] (LinearRootCoordinate318.Root a 0)))) :=
    IsFinite.SpecMap_iff.mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [factor,CommRingCat.ofHom_comp,Spec.map_comp]
  change IsFinite (Spec.map (LinearRootCoordinate318.coordinateEquiv a 0).toRingEquiv.toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap R[X] (LinearRootCoordinate318.Root a 0))))
  infer_instance

variable (B : Type*) [CommRing B] [Algebra R B] [Algebra R[X] B] [IsScalarTower R R[X] B]
theorem evaluate_factor :
    (Polynomial.aeval (R:=R) (algebraMap R B (↑a⁻¹:R)*(algebraMap R[X] B X)^2)).toRingHom=
      (algebraMap R[X] B).comp (squareCoordinate a).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [Polynomial.aeval_C,RingHom.comp_apply]
    change algebraMap R B r=algebraMap R[X] B (squareCoordinate a (C r))
    rw [squareCoordinate,Polynomial.aeval_C]
    exact IsScalarTower.algebraMap_apply R R[X] B r
  · rw [Polynomial.aeval_X,RingHom.comp_apply]
    change _=algebraMap R[X] B (squareCoordinate a X)
    rw [squareCoordinate,Polynomial.aeval_X,map_mul,map_pow]
    rfl
end UnitSquarePolynomialFinite318
