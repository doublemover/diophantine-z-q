module
public import ProjectivePrincipalUnitTrivialization318
public section
noncomputable section
namespace ProjectivePrincipalTrivializationNatural318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
variable (i : Fin F.size) (S T : CommRingCat.{0}) [Algebra R S] [Algebra R T]
  (g : S →ₐ[R] T) (a : H i →ₐ[R] S)

lemma unit_natural : (ProjectivePrincipalUnitTrivialization318.trivialization R P i T (g.comp a)).1=
    Units.map g.toMonoidHom (ProjectivePrincipalUnitTrivialization318.trivialization R P i S a).1 := rfl

/-- The actual local trivialization is natural on ALL coefficient maps,
including nonflat changes; the normalized algebra map is not chosen only
pointwise after a residue field or geometric closure. -/
lemma slice_natural : (ProjectivePrincipalUnitTrivialization318.trivialization R P i T (g.comp a)).2=
    g.comp (ProjectivePrincipalUnitTrivialization318.trivialization R P i S a).2 := by
  exact (ProjectiveParameterNormalizationNatural318.sliceMap R P S T g
    (a.comp (ProjectiveParameterPrincipalNormalization318.point R P i)) i
    (Units.map a.toMonoidHom (ProjectiveParameterPrincipalNormalization318.unit R P i)) rfl).symm

/-- Under the genuine unit/slice classification, the actual scheme
normalization morphism forgets exactly the UNIT coordinate and retains
the represented normalized slice, with its original inclusion. -/
lemma normalization_second : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
    ProjectiveParameterPrincipalNormalization318.map R P i=
    Spec.map (CommRingCat.ofHom
      (ProjectivePrincipalUnitTrivialization318.trivialization R P i S a).2.toRingHom) ≫
      ProjectiveParameterSliceGluing318.into R P i :=
  ProjectiveParameterNormalizationNatural318.map_natural R P (CommRingCat.of (H i)) S a
    (ProjectiveParameterPrincipalNormalization318.point R P i) i
    (ProjectiveParameterPrincipalNormalization318.unit R P i)
    (ProjectiveParameterPrincipalNormalization318.coordinate R P i)
end ProjectivePrincipalTrivializationNatural318
