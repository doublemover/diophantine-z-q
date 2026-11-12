module
public import ProjectiveParameterSliceTriplePullback318
public section
noncomputable section
namespace ProjectiveParameterSliceTripleLegs318
open ProjectiveParameterSliceTripleAlgebra318
universe u v
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "T" => algebra R P
variable (i j k : Fin F.size)

/-- The second actual overlap leg as an R-algebra map, represented by
restricting the universal triple point to its first/third coordinates. -/
@[expose] def secondMap : O i k →ₐ[R] T i j k :=
  (ProjectiveParameterSliceOverlapPoints318.points R P i k (T i j k)).symm
    (ProjectiveParameterSliceTriplePoints318.secondOverlap R P (T i j k) i j k
      (universal R P i j k))
lemma secondMap_point (a : A) : secondMap R P i j k
    (ProjectiveParameterSliceLocalization318.point R P i k a)=point R P i j k a :=
  ProjectiveParameterSliceOverlapPoints318.backward_point R P i k (T i j k) _ a

lemma rotation_point (a : A) : ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k
    (point R P j k i a)=
    (ProjectiveParameterSliceTriplePoints318.rotate R P (T i j k) i j k
      (universal R P i j k)).point a :=
  ProjectiveParameterSliceTripleRepresent318.backward_point R P j k i (T i j k) _ a

/-- Genuine algebra-map compatibility of cyclic triple rotation with the
already constructed pairwise transition; this is the GlueData leg equation. -/
lemma rotation_leg : (ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k).comp
    (secondMap R P j k i)=
    (overlapMap R P i j k).comp (ProjectiveParameterSliceLocalization318.transition R P i j) := by
  apply ProjectiveParameterSliceLocalizationIso318.hom_ext R P j i
  intro a
  change ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k
    (secondMap R P j k i (ProjectiveParameterSliceLocalization318.point R P j i a))=_
  rw [secondMap_point,rotation_point]
  change ProjectiveParameterUnitAction318.pointScale R P (T i j k)
    (((secondUnit R P i j k)⁻¹:(T i j k)ˣ):T i j k) (point R P i j k) a=
    overlapMap R P i j k (ProjectiveParameterSliceLocalization318.transition R P i j
      (ProjectiveParameterSliceLocalization318.point R P j i a))
  rw [ProjectiveParameterSliceLocalization318.transition_point]
  have h := ProjectiveParameterUnitAction318.pointScale_natural R P (O i j)
    (overlapMap R P i j k)
    (((ProjectiveParameterSliceLocalization318.unit R P i j)⁻¹:(O i j)ˣ):O i j)
    (ProjectiveParameterSliceLocalization318.point R P i j)
  exact (DFunLike.congr_fun h a).symm
end ProjectiveParameterSliceTripleLegs318
