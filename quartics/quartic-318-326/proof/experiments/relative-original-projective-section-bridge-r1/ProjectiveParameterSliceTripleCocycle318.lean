module
public import ProjectiveParameterSliceTripleRepresent318
public section
noncomputable section
namespace ProjectiveParameterSliceTripleCocycle318
open ProjectiveParameterSliceTripleAlgebra318
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "T" => algebra R P
variable (i j k : Fin F.size)

/-- Actual triple-overlap algebra transition induced by rotation of the
UNIVERSAL point in the literal iterated localization ring. -/
@[expose] def rotateMap : T j k i →ₐ[R] T i j k :=
  (ProjectiveParameterSliceTripleRepresent318.points R P j k i (T i j k)).symm
    (ProjectiveParameterSliceTriplePoints318.rotate R P (T i j k) i j k (universal R P i j k))

lemma forward_rotate : ProjectiveParameterSliceTripleRepresent318.forward R P j k i (T i j k)
    (rotateMap R P i j k)=ProjectiveParameterSliceTriplePoints318.rotate R P (T i j k)
      i j k (universal R P i j k) :=
  (ProjectiveParameterSliceTripleRepresent318.points R P j k i (T i j k)).apply_symm_apply _

/-- The SAME algebra transition induces the expected normalization on
EVERY coefficient test; this is not equality only on reduced points. -/
lemma action (S : Type w) [CommRing S] [Algebra R S] (g : T i j k →ₐ[R] S) :
    ProjectiveParameterSliceTripleRepresent318.forward R P j k i S (g.comp (rotateMap R P i j k))=
      ProjectiveParameterSliceTriplePoints318.rotate R P S i j k
        (ProjectiveParameterSliceTripleRepresent318.forward R P i j k S g) := by
  rw [ProjectiveParameterSliceTripleRepresent318.natural,forward_rotate,
    ProjectiveParameterSliceTriplePoints318.rotate_natural]
  rfl

/-- Exact cyclic algebra cocycle on the original triple LOCALIZATIONS.
Representation upgrades the previously proved normalized point identity
into equality of the genuine algebra maps on all elements. -/
lemma cycle : ((rotateMap R P i j k).comp (rotateMap R P j k i)).comp
    (rotateMap R P k i j)=AlgHom.id R (T i j k) := by
  apply (ProjectiveParameterSliceTripleRepresent318.points R P i j k (T i j k)).injective
  change ProjectiveParameterSliceTripleRepresent318.forward R P i j k (T i j k)
    (((rotateMap R P i j k).comp (rotateMap R P j k i)).comp (rotateMap R P k i j))=_
  rw [action,action,forward_rotate]
  have h := ProjectiveParameterSliceTriplePoints318.rotate_three R P (T i j k)
    i j k (universal R P i j k)
  exact h
end ProjectiveParameterSliceTripleCocycle318
