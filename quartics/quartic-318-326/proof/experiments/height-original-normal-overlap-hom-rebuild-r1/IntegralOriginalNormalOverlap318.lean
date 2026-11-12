module
public import LaurentCoordinateInversion318
public import IntegralClosureScalarEquiv318
public import IntegralInfinityReciprocalScalar318
public import IntegralNormalReciprocalForms318
public section
noncomputable section
namespace IntegralOriginalNormalOverlap318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "B" => OpenOrder R a d
local notation "F" => Base R a d
local notation "u" => IntegralNormalReciprocalForms318.coordinateUnit R a d

lemma coordinate_unit : IsUnit (algebraMap P B X) := by
  have h : (u:B)=algebraMap P B X :=
    (IntegralNormalReciprocalForms318.coordinateUnit_value R a d).trans
      (IsScalarTower.algebraMap_apply P F B X).symm
  rw [←h]
  exact u.isUnit

@[expose] def finiteMap : S →+* B :=
  IsLocalization.Away.lift (X:P) (coordinate_unit R a d)
@[expose] def infinityMap : S →+* B :=
  (finiteMap R a d).comp (LaurentCoordinateInversion318.tau R).toRingHom

lemma finite_polynomial (q : P) :
    finiteMap R a d (algebraMap P S q)=algebraMap P B q :=
  IsLocalization.Away.lift_eq (X:P) (coordinate_unit R a d) q

lemma finite_coordinate : finiteMap R a d (LaurentCoordinateInversion318.coordinate R:S)=(u:B) := by
  rw [NormalizedReciprocalLaurent318.coordinate_value,finite_polynomial,
    IntegralNormalReciprocalForms318.coordinateUnit_value]
  exact IsScalarTower.algebraMap_apply P F B X

lemma finite_inverse : finiteMap R a d (↑(LaurentCoordinateInversion318.coordinate R)⁻¹:S)=
    (↑u⁻¹:B) :=
  IntegralInfinityBaseEquiv318.map_unit_inverse (finiteMap R a d)
    (LaurentCoordinateInversion318.coordinate R) u (finite_coordinate R a d)

lemma infinity_polynomial : (infinityMap R a d).comp (algebraMap P S)=
    IntegralInfinityReciprocalScalar318.sourceMap R a d := by
  apply Polynomial.ringHom_ext
  · intro r
    change finiteMap R a d (LaurentCoordinateInversion318.tau R
      (algebraMap P S (C r)))=_
    rw [LaurentCoordinateInversion318.polynomial,
      NormalizedReciprocalLaurent318.reciprocalMap,Polynomial.aeval_C]
    change finiteMap R a d (algebraMap R S r)=_
    change finiteMap R a d (algebraMap P S (C r))=_
    rw [finite_polynomial]
    change algebraMap P B (C r)=algebraMap F B
      (IntegralInfinityReciprocalScalar318.baseMap R a d (C r))
    rw [IntegralInfinityReciprocalScalar318.baseMap_value]
    simp only [IntegralReciprocalBase318.reciprocalPolynomial,Polynomial.aeval_C] <;> rfl
  · change finiteMap R a d (LaurentCoordinateInversion318.tau R
      (algebraMap P S X))=_
    rw [←NormalizedReciprocalLaurent318.coordinate_value,
      LaurentCoordinateInversion318.coordinate_inverse,finite_inverse]
    exact (IntegralNormalReciprocalForms318.reciprocal_polynomial R a d).symm

lemma scalar_square : (infinityMap R a d).comp (LaurentCoordinateInversion318.tau R).toRingHom=
    finiteMap R a d := by
  apply RingHom.ext
  intro s
  change finiteMap R a d (LaurentCoordinateInversion318.tau R
    (LaurentCoordinateInversion318.tau R s))=finiteMap R a d s
  rw [LaurentCoordinateInversion318.twice]

abbrev FiniteOverlap := IntegralClosureAlongRingMap318.Closure (finiteMap R a d)
abbrev InfinityOverlap := IntegralClosureAlongRingMap318.Closure (infinityMap R a d)

@[expose] def overlapEquiv : FiniteOverlap R a d ≃+* InfinityOverlap R a d :=
  IntegralClosureScalarEquiv318.equivalence (finiteMap R a d) (infinityMap R a d)
    (LaurentCoordinateInversion318.tau R) (scalar_square R a d)

lemma overlap_ambient (z : FiniteOverlap R a d) : (overlapEquiv R a d z:B)=z.val := rfl
end IntegralOriginalNormalOverlap318
