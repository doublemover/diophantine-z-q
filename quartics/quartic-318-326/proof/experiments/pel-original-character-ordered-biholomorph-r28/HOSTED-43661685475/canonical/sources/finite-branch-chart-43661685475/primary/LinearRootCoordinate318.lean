module
public import ContactGenericFiber318
public import Mathlib.Algebra.Polynomial.RingDivision
public section
noncomputable section
namespace LinearRootCoordinate318
set_option maxHeartbeats 400000
open Polynomial QuadraticPresentation318
variable {R:Type*} [CommRing R] (c:Rˣ) (a:R)
@[expose] def parameter : R[X] := C (c:R)*(X-C a)
abbrev Root:=RootRing (parameter c a)
@[expose] def baseSubstitution : R[X]→ₐ[R]R[X] :=
  Polynomial.aeval (C (↑(c⁻¹):R)*X^2+C a)

/-- The original linear-base quadratic quotient has an actual polynomial
coordinate; this is not an assumed local square coordinate. -/
@[expose] def forward : Root c a→ₐ[R]R[X] :=
  AdjoinRoot.liftAlgHom (polynomial (parameter c a)) (baseSubstitution c a) X (by
    simp only [polynomial,Polynomial.eval₂_sub,Polynomial.eval₂_pow,
      Polynomial.eval₂_X,parameter,map_mul,map_sub]
    simp [baseSubstitution,Polynomial.aeval_C,Polynomial.aeval_X,
      ←mul_assoc,←map_mul])

@[simp] theorem forward_root : forward c a (AdjoinRoot.root (polynomial (parameter c a)))=X :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def inverse : R[X]→ₐ[R]Root c a :=
  Polynomial.aeval (AdjoinRoot.root (polynomial (parameter c a)))

@[simp] theorem inverse_X : inverse c a X=AdjoinRoot.root (polynomial (parameter c a)) :=
  Polynomial.aeval_X _

theorem inverse_base : inverse c a (baseSubstitution c a X)=
    AdjoinRoot.of (polynomial (parameter c a)) X := by
  simp only [baseSubstitution,Polynomial.aeval_X,map_add,map_mul,map_pow,
    inverse_X]
  simp only [inverse,Polynomial.aeval_C]
  rw [root_square]
  change algebraMap R (Root c a) (↑(c⁻¹):R)*
    (algebraMap R[X] (Root c a)) (C (c:R)*(X-C a))+algebraMap R (Root c a) a=_
  rw [map_mul,map_sub]
  have hc:algebraMap R[X] (Root c a) (C (c:R))=algebraMap R (Root c a) (c:R) := rfl
  have ha:algebraMap R[X] (Root c a) (C a)=algebraMap R (Root c a) a := rfl
  rw [hc,ha,←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul,sub_add_cancel]
  rfl

@[expose] def coordinateEquiv : Root c a≃ₐ[R]R[X] :=
  AlgEquiv.ofAlgHom (forward c a) (inverse c a)
    (by
      apply Polynomial.algHom_ext
      simp [AlgHom.comp_apply])
    (by
      apply AdjoinRoot.algHom_ext'
      · apply Polynomial.algHom_ext
        change inverse c a (forward c a (AdjoinRoot.of _ X))=AdjoinRoot.of _ X
        change inverse c a ((AdjoinRoot.liftAlgHom (polynomial (parameter c a)) (baseSubstitution c a) X _) (AdjoinRoot.of _ X))=_
        rw [AdjoinRoot.liftAlgHom_of]
        exact inverse_base c a
      · simp [AlgHom.comp_apply])

end LinearRootCoordinate318

namespace LinearRootCoordinate318
open Polynomial QuadraticPresentation318
variable {R:Type*} [CommRing R] (c:Rˣ) (a:R)

@[simp] theorem forward_base (p:R[X]) :
    forward c a (AdjoinRoot.of (polynomial (parameter c a)) p)=baseSubstitution c a p :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ _

theorem coordinate_base (p:R[X]) :
    coordinateEquiv c a (algebraMap R[X] (Root c a) p)=baseSubstitution c a p :=
  forward_base c a p

/-- The original base parameter, in the actual quotient coordinate. -/
theorem coordinate_contact :
    coordinateEquiv c a (algebraMap R[X] (Root c a) (X-C a))=C (↑(c⁻¹):R)*X^2 := by
  rw [coordinate_base]
  simp [baseSubstitution]

/-- Each other branch polynomial has its exact quadratic expression. -/
theorem coordinate_other (d:Rˣ) (b:R) :
    coordinateEquiv c a (algebraMap R[X] (Root c a) (parameter d b))=
      C ((d:R)*(↑(c⁻¹):R))*X^2+C ((d:R)*(a-b)) := by
  rw [coordinate_base]
  simp only [parameter,map_mul,map_sub,baseSubstitution,Polynomial.aeval_C,
    Polynomial.aeval_X,Polynomial.algebraMap_eq,map_mul,map_sub]
  ring

@[expose] def branchEvaluation : Root c a→ₐ[R]R :=
  (Polynomial.aeval (0:R)).comp (coordinateEquiv c a).toAlgHom

@[simp] theorem branchEvaluation_root :
    branchEvaluation c a (AdjoinRoot.root (polynomial (parameter c a)))=0 := by
  simp [branchEvaluation,coordinateEquiv]

@[simp] theorem branchEvaluation_base (p:R[X]) :
    branchEvaluation c a (algebraMap R[X] (Root c a) p)=Polynomial.eval a p := by
  change Polynomial.aeval (0:R) (coordinateEquiv c a (algebraMap R[X] (Root c a) p))=_
  rw [coordinate_base]
  change Polynomial.eval 0 (p.comp (C (↑(c⁻¹):R)*X^2+C a))=_
  rw [Polynomial.eval_comp]
  simp

@[simp] theorem branchEvaluation_other (d:Rˣ) (b:R) :
    branchEvaluation c a (algebraMap R[X] (Root c a) (parameter d b))=(d:R)*(a-b) := by
  rw [branchEvaluation_base]
  simp [parameter]

end LinearRootCoordinate318

namespace LinearRootCoordinate318
open Polynomial QuadraticPresentation318
variable {R:Type*} [CommRing R] (c:Rˣ) (a:R)

theorem contact_square :
    algebraMap R[X] (Root c a) (X-C a)=
      algebraMap R (Root c a) (↑(c⁻¹):R)*
        AdjoinRoot.root (polynomial (parameter c a))^2 := by
  apply (coordinateEquiv c a).injective
  rw [coordinate_contact,map_mul,map_pow]
  change C (↑(c⁻¹):R)*X^2=
    coordinateEquiv c a (algebraMap R (Root c a) (↑(c⁻¹):R))*
      forward c a (AdjoinRoot.root (polynomial (parameter c a)))^2
  rw [AlgEquiv.commutes,forward_root]
  rfl

/-- The coordinate equation has exactly a double zero, not merely an even
or lower-bounded order. -/
theorem coordinate_contact_multiplicity [IsDomain R] :
    Polynomial.rootMultiplicity (0:R)
      (coordinateEquiv c a (algebraMap R[X] (Root c a) (X-C a)))=2 := by
  rw [coordinate_contact]
  simpa only [map_zero,sub_zero,Polynomial.rootMultiplicity_C,zero_add] using
    (Polynomial.rootMultiplicity_mul_X_sub_C_pow (a:=(0:R)) (n:=2)
      (p:=C (↑(c⁻¹):R)) (Polynomial.C_ne_zero.mpr c⁻¹.ne_zero))
end LinearRootCoordinate318
