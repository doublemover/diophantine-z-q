module
public import ProjectiveParameterSliceOverlapPoints318
public section
noncomputable section
namespace ProjectiveParameterOverlapLegs318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
variable (i j : Fin F.size) (S : Type w) [CommRing S] [Algebra R S]
  (q : ProjectiveParameterSliceOverlap318.Point R P S i j)
local notation "k" => ProjectiveParameterSliceOverlapPoints318.backward R P i j S q

lemma first : k.comp (IsScalarTower.toAlgHom R (B i) (O i j))=
    ProjectiveParameterSliceOverlapPoints318.sliceMap R P i j S q := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change k (ProjectiveParameterSliceLocalization318.point R P i j a)=_
  rw [ProjectiveParameterSliceOverlapPoints318.backward_point,
    ProjectiveParameterSliceOverlapPoints318.sliceMap_mk]

lemma mapped_point : k.comp (ProjectiveParameterSliceLocalization318.point R P i j)=q.point := by
  apply AlgHom.ext
  exact ProjectiveParameterSliceOverlapPoints318.backward_point R P i j S q
lemma mapped_unit : Units.map k.toMonoidHom (ProjectiveParameterSliceLocalization318.unit R P i j)=
    q.secondUnit := by
  apply Units.ext
  change k (ProjectiveParameterSliceLocalization318.unit R P i j:O i j)=(q.secondUnit:S)
  rw [ProjectiveParameterSliceLocalization318.unit_val,
    ProjectiveParameterSliceOverlapPoints318.backward_point,q.second_eq]

/-- The ACTUAL localized overlap point, followed by the actual opposite
transition, induces the opposite normalized slice map on every test ring. -/
lemma second : (k.comp (ProjectiveParameterSliceLocalization318.transition R P i j)).comp
    (IsScalarTower.toAlgHom R (B j) (O j i))=
    ProjectiveParameterSliceOverlapPoints318.sliceMap R P j i S
      (ProjectiveParameterSliceOverlap318.transition R P S i j q) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change k (ProjectiveParameterSliceLocalization318.transition R P i j
    (ProjectiveParameterSliceLocalization318.point R P j i a))=_
  rw [ProjectiveParameterSliceLocalization318.transition_point,
    ProjectiveParameterSliceOverlapPoints318.sliceMap_mk]
  have hn := DFunLike.congr_fun (ProjectiveParameterUnitAction318.pointScale_natural R P (O i j) k
    (((ProjectiveParameterSliceLocalization318.unit R P i j)⁻¹:(O i j)ˣ):O i j)
    (ProjectiveParameterSliceLocalization318.point R P i j)) a
  rw [mapped_point R P i j S q] at hn
  have hu : k (((ProjectiveParameterSliceLocalization318.unit R P i j)⁻¹:(O i j)ˣ):O i j)=
      ((q.secondUnit⁻¹:Sˣ):S) := by
    change (((Units.map k.toMonoidHom (ProjectiveParameterSliceLocalization318.unit R P i j))⁻¹:Sˣ):S)=_
    rw [mapped_unit R P i j S q]
  rw [hu] at hn
  exact hn
end ProjectiveParameterOverlapLegs318
