module
public import ProjectiveParameterSliceTripleAlgebra318
public section
noncomputable section
namespace ProjectiveParameterSliceTripleRepresent318
open ProjectiveParameterSliceTripleAlgebra318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "x" => ProjectiveParameterZeroCoordinates318.coordinate R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
variable (i j k : Fin F.size) (S : Type w) [CommRing S] [Algebra R S]
local notation "T" => algebra R P i j k
local notation "Q" => ProjectiveParameterSliceTriplePoints318.Point R P S i j k

@[expose] def forward (a : T →ₐ[R] S) : Q :=
  ProjectiveParameterSliceTriplePoints318.map R P T a i j k (universal R P i j k)
@[expose] def overlap (a : Q) : O i j →ₐ[R] S :=
  (ProjectiveParameterSliceOverlapPoints318.points R P i j S).symm
    (ProjectiveParameterSliceTriplePoints318.firstOverlap R P S i j k a)
lemma overlap_point (a : Q) (z : A) : overlap R P i j k S a
    (ProjectiveParameterSliceLocalization318.point R P i j z)=a.point z :=
  ProjectiveParameterSliceOverlapPoints318.backward_point R P i j S _ z
lemma overlap_coordinate (a : Q) : overlap R P i j k S a (coordinate R P i j k)=(a.thirdUnit:S) := by
  rw [coordinate,overlap_point,a.third_eq]

@[expose] def backward (a : Q) : T →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (coordinate R P i j k)
    (show IsUnit (overlap R P i j k S a (coordinate R P i j k)) from by
      rw [overlap_coordinate]
      exact a.thirdUnit.isUnit)
lemma backward_point (a : Q) (z : A) : backward R P i j k S a (point R P i j k z)=a.point z := by
  change backward R P i j k S a (algebraMap (O i j) T
    (ProjectiveParameterSliceLocalization318.point R P i j z))=_
  rw [backward,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,overlap_point]

/-- The actual iterated-localization algebra represents ALL triple points,
so the triple cocycle is meaningful on schemes with nilpotents as well. -/
@[expose] def points : (T →ₐ[R] S) ≃ Q where
  toFun := forward R P i j k S
  invFun := backward R P i j k S
  left_inv a := by
    apply hom_ext R P i j k
    intro z
    rw [backward_point]
    rfl
  right_inv a := by
    apply ProjectiveParameterSliceTriplePoints318.point_ext
    · apply AlgHom.ext
      intro z
      exact backward_point R P i j k S a z
    · apply Units.ext
      change backward R P i j k S a (secondUnit R P i j k:T)=(a.secondUnit:S)
      change backward R P i j k S a (point R P i j k (x j))=(a.secondUnit:S)
      rw [backward_point,a.second_eq]
    · apply Units.ext
      change backward R P i j k S a (thirdUnit R P i j k:T)=(a.thirdUnit:S)
      change backward R P i j k S a (point R P i j k (x k))=(a.thirdUnit:S)
      rw [backward_point,a.third_eq]

lemma natural {U : Type*} [CommRing U] [Algebra R U] (g : S →ₐ[R] U) (a : T →ₐ[R] S) :
    forward R P i j k U (g.comp a)=ProjectiveParameterSliceTriplePoints318.map R P S g i j k
      (forward R P i j k S a) := by
  exact (ProjectiveParameterSliceTriplePoints318.map_comp R P T a g i j k
    (universal R P i j k)).symm
end ProjectiveParameterSliceTripleRepresent318
