module
public import ProjectiveParameterOverlapLegs318
public import ProjectiveParameterSliceGluing318
public section
noncomputable section
namespace ProjectiveParameterOverlapSchemePoints318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i j : Fin F.size) (S : CommRingCat.{0}) [Algebra R S]
  (q : ProjectiveParameterSliceOverlap318.Point R P S i j)
local notation "k" => ProjectiveParameterSliceOverlapPoints318.backward R P i j S q
local notation "inc" => ProjectiveParameterSliceSchemes318.inclusion R P
local notation "u" => ProjectiveParameterSliceGluing318.into R P
local notation "a" => ProjectiveParameterSliceOverlapPoints318.sliceMap R P i j S q
local notation "b" => ProjectiveParameterSliceOverlapPoints318.sliceMap R P j i S
  (ProjectiveParameterSliceOverlap318.transition R P S i j q)

lemma first : Spec.map (CommRingCat.ofHom k.toRingHom) ≫ inc i j=
    Spec.map (CommRingCat.ofHom a.toRingHom) := by
  rw [ProjectiveParameterSliceSchemes318.inclusion,← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
    (ProjectiveParameterOverlapLegs318.first R P i j S q)

lemma second : Spec.map (CommRingCat.ofHom k.toRingHom) ≫
    (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom ≫ inc j i=
    Spec.map (CommRingCat.ofHom b.toRingHom) := by
  change Spec.map (CommRingCat.ofHom k.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveParameterSliceLocalization318.transition R P i j).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap _ _))=_
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
    (ProjectiveParameterOverlapLegs318.second R P i j S q)

/-- The two ACTUAL normalized chart maps give the same morphism into
the glued parameter scheme, for arbitrary possibly nonreduced test rings.
The specified localized overlap and original GlueData equation are used. -/
lemma into_eq : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ u i=
    Spec.map (CommRingCat.ofHom b.toRingHom) ≫ u j := by
  rw [← first R P i j S q,← second R P i j S q]
  simp only [Category.assoc,ProjectiveParameterSliceGluing318.glue_condition]
end ProjectiveParameterOverlapSchemePoints318
