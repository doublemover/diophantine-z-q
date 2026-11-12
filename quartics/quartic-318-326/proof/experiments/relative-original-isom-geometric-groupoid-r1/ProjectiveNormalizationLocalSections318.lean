module
public import ProjectivePrincipalLaurentScheme318
public import ProjectiveParameterGlobalNormalization318
public section
noncomputable section
namespace ProjectiveNormalizationLocalSections318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
variable (i : Fin F.size)

/-- Set the ACTUAL unit coordinate equal to one and retain the identity
point of the ORIGINAL normalized slice, over its full possibly
nonreduced coordinate ring. -/
@[expose] def ringSection : H i →ₐ[R] B i :=
  (ProjectivePrincipalUnitTrivialization318.trivialization R P i (CommRingCat.of (B i))).symm
    (1,AlgHom.id R (B i))
lemma normalized_ringSection :
    (ProjectivePrincipalUnitTrivialization318.trivialization R P i
      (CommRingCat.of (B i)) (ringSection R P i)).2=AlgHom.id R (B i) :=
  congrArg Prod.snd
    ((ProjectivePrincipalUnitTrivialization318.trivialization R P i
      (CommRingCat.of (B i))).apply_symm_apply (1,AlgHom.id R (B i)))

@[expose] def sectionMap : ProjectiveParameterSliceSchemes318.chart R P i ⟶
    (ProjectiveParameterPrincipalCover318.locus R P).toScheme :=
  Spec.map (CommRingCat.ofHom (ringSection R P i).toRingHom) ≫
    ProjectiveParameterPrincipalCover318.into R P i

/-- Genuine local sections of the SAME global normalization morphism,
on the proved full cover of the glued projective parameter. -/
@[reassoc] lemma section_normalization : sectionMap R P i ≫
    ProjectiveParameterGlobalNormalization318.map R P=
    ProjectiveParameterSliceGluing318.into R P i := by
  rw [sectionMap,Category.assoc,ProjectiveParameterGlobalNormalization318.on_chart]
  rw [ProjectivePrincipalTrivializationNatural318.normalization_second,
    normalized_ringSection]
  have hi : Spec.map (CommRingCat.ofHom (AlgHom.id R (B i)).toRingHom)=
      𝟙 (Spec (CommRingCat.of (B i))) := Spec.map_id _
  rw [hi,Category.id_comp]

/-- Normalization from the ORIGINAL nonzero vector open is genuinely
surjective onto the SAME glued parameter, without any positive-rank
hypothesis on the coefficient base. This does not assert that the
parameter itself is surjective over that base. -/
theorem surjective : Surjective (ProjectiveParameterGlobalNormalization318.map R P) := by
  constructor
  intro x
  obtain ⟨i,y,hy⟩ := ProjectiveParameterSliceGluing318.jointly_surjective R P x
  refine ⟨sectionMap R P i y,?_⟩
  have h := congrArg (fun a => a y) (section_normalization R P i)
  exact h.trans hy
end ProjectiveNormalizationLocalSections318
