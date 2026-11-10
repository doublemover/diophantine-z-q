module
public import ProjectiveParameterSliceGluing318
public section
noncomputable section
namespace ProjectiveParameterSliceBase318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProjectiveParameterSliceGluing318
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

/-- Actual structural morphism of the glued normalized-slice scheme.
Every chart map is the original coefficient-algebra map. -/
@[expose] def projection : scheme R P ⟶ Spec R := by
  fapply Multicoequalizer.desc
  · exact ProjectiveParameterSliceSchemes318.projection R P
  rintro ⟨i,j⟩
  change ProjectiveParameterSliceSchemes318.inclusion R P i j ≫
    ProjectiveParameterSliceSchemes318.projection R P i=
    ((ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom ≫
      ProjectiveParameterSliceSchemes318.inclusion R P j i) ≫
        ProjectiveParameterSliceSchemes318.projection R P j
  rw [Category.assoc]
  exact (ProjectiveParameterSliceSchemes318.relative_overlap R P i j).2.symm

@[reassoc] lemma into_projection (i : Fin F.size) :
    into R P i ≫ projection R P=ProjectiveParameterSliceSchemes318.projection R P i :=
  Multicoequalizer.π_desc _ _ _ _ _
end ProjectiveParameterSliceBase318
