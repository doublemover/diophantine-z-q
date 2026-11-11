module
public import ProjectiveParameterSliceOverlap318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ProjectiveParameterSliceLocalization318
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
variable (i j : Fin F.size)

@[expose] def coordinate : B i := Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P i) (x j)
abbrev algebra := Localization.Away (coordinate R P i j)
local notation "O" => algebra R P i j
instance baseAlgebra : Algebra R O :=
  ((algebraMap (B i) O).comp (algebraMap R (B i))).toAlgebra
instance baseTower : IsScalarTower R (B i) O := IsScalarTower.of_algebraMap_eq' rfl

/-- The actual original symmetric-algebra point in the localized slice
ring, retaining the quotient by x_i-1 and the localization at x_j. -/
@[expose] def point : A →ₐ[R] O :=
  (IsScalarTower.toAlgHom R (B i) O).comp
    (Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R P i))
lemma first : point R P i j (x i)=1 := by
  change algebraMap (B i) O (Ideal.Quotient.mk _ (x i))=1
  rw [ProjectiveParameterSliceAlgebra318.coordinate_one,map_one]
lemma second : point R P i j (x j)=algebraMap (B i) O (coordinate R P i j) := rfl

/-- A literal unit, with inverse given by the same away-localization
inverse. No nonzero-element-to-unit step is made. -/
@[expose] def unit : Oˣ where
  val := algebraMap (B i) O (coordinate R P i j)
  inv := IsLocalization.Away.invSelf (coordinate R P i j)
  val_inv := IsLocalization.Away.mul_invSelf _
  inv_val := by rw [mul_comm,IsLocalization.Away.mul_invSelf]
lemma unit_val : (unit R P i j : O)=point R P i j (x j) := rfl

@[expose] def overlapPoint : ProjectiveParameterSliceOverlap318.Point R P O i j :=
  ⟨point R P i j,first R P i j,unit R P i j,(unit_val R P i j).symm⟩

/-- Genuine algebra map from the opposite slice, constructed by its
represented normalized-point property, not an abstract bijection. -/
@[expose] def oppositeSlice : B j →ₐ[R] O :=
  (ProjectiveParameterSliceAlgebra318.points R P j O).symm
    ⟨(ProjectiveParameterSliceOverlap318.transition R P O i j
        (overlapPoint R P i j)).point,
      (ProjectiveParameterSliceOverlap318.transition R P O i j
        (overlapPoint R P i j)).first_eq⟩
lemma oppositeSlice_mk (a : A) :
    oppositeSlice R P i j (Ideal.Quotient.mk (ProjectiveParameterSliceAlgebra318.ideal R P j) a)=
      ProjectiveParameterUnitAction318.pointScale R P O ((unit R P i j)⁻¹:Oˣ) (point R P i j) a := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ a)=_
  rw [Ideal.Quotient.lift_mk]
  rfl
lemma opposite_coordinate : oppositeSlice R P i j (coordinate R P j i)=
    (((unit R P i j)⁻¹:Oˣ):O) := by
  rw [coordinate,oppositeSlice_mk,ProjectiveParameterUnitSlice318.scale_coordinate,first,mul_one]

/-- The opposite normalized coordinate is invertible, so the algebra
map extends to the ACTUAL opposite localized overlap. -/
@[expose] def transition : algebra R P j i →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (coordinate R P j i)
    (show IsUnit (oppositeSlice R P i j (coordinate R P j i)) from by
      rw [opposite_coordinate]
      exact ((unit R P i j)⁻¹).isUnit)
lemma transition_localized (b : B j) :
    transition R P i j (algebraMap (B j) (algebra R P j i) b)=oppositeSlice R P i j b := by
  exact IsLocalization.Away.lift_eq _ _ b
lemma transition_point (a : A) :
    transition R P i j (point R P j i a)=
      ProjectiveParameterUnitAction318.pointScale R P O ((unit R P i j)⁻¹:Oˣ) (point R P i j) a := by
  change transition R P i j (algebraMap (B j) (algebra R P j i)
    (Ideal.Quotient.mk _ a))=_
  rw [transition_localized,oppositeSlice_mk]
end ProjectiveParameterSliceLocalization318
