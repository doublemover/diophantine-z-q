module
public import ProjectiveParameterSliceTripleLegs318
public import ProjectiveParameterSliceSelf318
public section
noncomputable section
namespace ProjectiveParameterSliceTripleSchemes318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "T" => ProjectiveParameterSliceTripleAlgebra318.algebra R P
variable (i j k : Fin F.size)
local notation "X" => ProjectiveParameterSliceTriplePullback318.scheme R P

lemma second_ring : (ProjectiveParameterSliceTripleLegs318.secondMap R P i j k).toRingHom=
    (AffineAwayPullback318.arrow (CommRingCat.ofHom (algebraMap (B i) (O i j)))
      (ProjectiveParameterSliceLocalization318.coordinate R P i k)).hom := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (ProjectiveParameterSliceLocalization318.coordinate R P i k))
  apply RingHom.ext
  intro b
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective b
  change ProjectiveParameterSliceTripleLegs318.secondMap R P i j k
    (ProjectiveParameterSliceLocalization318.point R P i k a)=_
  rw [ProjectiveParameterSliceTripleLegs318.secondMap_point,AffineAwayPullback318.arrow_base]
  rfl
lemma second_eq : ProjectiveParameterSliceTriplePullback318.second R P i j k=
    Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceTripleLegs318.secondMap R P i j k).toRingHom) := by
  rw [second_ring]
  rfl

@[expose] def rotation : X i j k ⟶ X j k i :=
  Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k).toRingHom)

/-- Actual scheme leg compatibility after identifying the literal triple
localization with the required pairwise-overlap pullback. -/
@[reassoc] lemma leg : rotation R P i j k ≫ ProjectiveParameterSliceTriplePullback318.second R P j k i=
    ProjectiveParameterSliceTriplePullback318.first R P i j k ≫
      (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom := by
  rw [second_eq]
  change Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceTripleLegs318.secondMap R P j k i).toRingHom)=
    Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceTripleAlgebra318.overlapMap R P i j k).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceLocalization318.transition R P i j).toRingHom)
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (ProjectiveParameterSliceTripleLegs318.rotation_leg R P i j k)

/-- The genuine scheme triple rotations satisfy the exact cyclic cocycle.
This uses equality of actual algebra maps, not bijectivity on points. -/
lemma cycle : rotation R P i j k ≫ rotation R P j k i ≫ rotation R P k i j=𝟙 (X i j k) := by
  unfold rotation
  rw [← Spec.map_comp,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((ProjectiveParameterSliceTripleCocycle318.rotateMap R P i j k).comp
      (ProjectiveParameterSliceTripleCocycle318.rotateMap R P j k i)).comp
      (ProjectiveParameterSliceTripleCocycle318.rotateMap R P k i j)).toRingHom)=_
  rw [ProjectiveParameterSliceTripleCocycle318.cycle]
  exact Spec.map_id _
end ProjectiveParameterSliceTripleSchemes318
