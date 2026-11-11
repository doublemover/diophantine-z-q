module
public import IntegralOriginalSectionRatios318
public section
noncomputable section
namespace IntegralPencilScalarMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318 IntegralWholeOrderOpenMaps318
open IntegralWholeOrderScalarMaps318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The original t is a unit on the full Laurent overlap, with the original
inverse twist and the SQUARE of the signed pivot root. -/
@[expose] def originalTUnit : (CommonOrder R c)ˣ :=
  Units.map (algebraMap R (CommonOrder R c)).toMonoidHom (c 0)⁻¹ * (commonY R c)^2
@[expose] def finiteCoordinate : R[X] →ₐ[R] FiniteOrder R c :=
  Polynomial.aeval (algebraMap R (FiniteOrder R c) (↑(c 0)⁻¹:R) *
    (algebraMap R[X] (FiniteOrder R c) X)^2)
@[expose] def reciprocalCoordinate : R[X] →ₐ[R] InfinityOrder R c :=
  Polynomial.aeval (algebraMap R (InfinityOrder R c) (↑(c 0)⁻¹:R) *
    (algebraMap R[X] (InfinityOrder R c) X)^2)

theorem finite_evaluation : (finiteMap R c).comp (finiteCoordinate R c).toRingHom=
    (Polynomial.aeval (R:=R) (originalTUnit R c:CommonOrder R c)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change finiteMap R c (finiteCoordinate R c (C r))=_
    rw [finiteCoordinate,Polynomial.aeval_C]
    change finiteMap R c (algebraMap R[X] (FiniteOrder R c) (C r))=_
    rw [finite_polynomial,Polynomial.aeval_C]
    rfl
  · change finiteMap R c (finiteCoordinate R c X)=_
    rw [finiteCoordinate,Polynomial.aeval_X,map_mul,map_pow]
    change finiteMap R c (algebraMap R[X] (FiniteOrder R c) (C (↑(c 0)⁻¹:R))) *
      (finiteMap R c (algebraMap R[X] (FiniteOrder R c) X))^2=_
    rw [finite_polynomial,finite_polynomial,Polynomial.aeval_X]
    change _=algebraMap R (CommonOrder R c) (↑(c 0)⁻¹:R) *
      (algebraMap (Laurent R) (CommonOrder R c) (y R:Laurent R))^2
    rw [y_value]
    rfl

/-- Exact unit calculation for the original reciprocal ratio, independent
of any normalization of the concrete nested tensor-ring expressions. -/
theorem inverse_square {A : Type*} [CommRing A] (a y : Aˣ) :
    (↑a⁻¹:A)*((a:A)*(↑y⁻¹:A))^2=(↑(a⁻¹*y^2)⁻¹:A) := by
  have h : a⁻¹*(a*y⁻¹)^2=(a⁻¹*y^2)⁻¹ := by
    simp only [mul_pow,mul_inv_rev,inv_pow,inv_inv]
    calc
      _ = a*(y⁻¹)^2 := by group
      _ = (y⁻¹)^2*a := by ac_rfl
  exact congrArg (fun z : Aˣ => (z:A)) h

theorem reciprocal_evaluation :
    (infinityMap R c).comp (reciprocalCoordinate R c).toRingHom=
      (Polynomial.aeval (R:=R) (↑(originalTUnit R c)⁻¹:CommonOrder R c)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change infinityMap R c (reciprocalCoordinate R c (C r))=_
    rw [reciprocalCoordinate,Polynomial.aeval_C]
    change infinityMap R c (algebraMap R[X] (InfinityOrder R c) (C r))=_
    rw [infinity_polynomial]
    simp only [reciprocalMap,Polynomial.aeval_C]
    rfl
  · change infinityMap R c (reciprocalCoordinate R c X)=_
    rw [reciprocalCoordinate,Polynomial.aeval_X,map_mul,map_pow]
    change infinityMap R c (algebraMap R[X] (InfinityOrder R c) (C (↑(c 0)⁻¹:R))) *
      (infinityMap R c (algebraMap R[X] (InfinityOrder R c) X))^2=_
    rw [infinity_polynomial,infinity_polynomial,Polynomial.aeval_X]
    simp only [reciprocalMap,Polynomial.aeval_C,Polynomial.aeval_X,u,map_mul]
    exact inverse_square
      (Units.map (algebraMap R (CommonOrder R c)).toMonoidHom (c 0)) (commonY R c)
end IntegralPencilScalarMaps318
