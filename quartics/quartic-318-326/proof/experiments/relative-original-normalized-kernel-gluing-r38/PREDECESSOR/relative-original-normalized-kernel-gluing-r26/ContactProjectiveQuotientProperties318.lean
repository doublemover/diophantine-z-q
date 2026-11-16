module
public import ContactProjectiveQuotientIdealSheaf318
public import ContactRelativeOriginalSmoothProper318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace ContactProjectiveQuotientProperties318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveQuotientData318 ContactProjectiveQuotientGluing318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (D : Datum R c)
abbrev finiteProjection : finiteFamily R c D ⟶ Spec R := finiteInto R c D ≫
  Spec.map (CommRingCat.ofHom (algebraMap R (finiteRing R c)))
abbrev infinityProjection : infinityFamily R c D ⟶ Spec R := infinityInto R c D ≫
  Spec.map (CommRingCat.ofHom (algebraMap R (infinityRing R c)))
@[reassoc] lemma finite_projection : finiteChart R c D ≫ projection R c D=finiteProjection R c D := by
  rw [projection,← Category.assoc,(finite_square R c D).w,Category.assoc,
    RelativeOriginalAffineChart318.over_test]
@[reassoc] lemma infinity_projection : infinityChart R c D ≫ projection R c D=infinityProjection R c D := by
  rw [projection,← Category.assoc,(infinity_square R c D).w,Category.assoc,
    RelativeOriginalAffineChart318.over_test]
/-- Properness belongs to the whole closed projective quotient, regardless
of whether its affine chart pieces are finite over the coefficient base. -/
instance proper : IsProper (projection R c D) := by
  change IsProper (into R c D ≫ ContactRelativeStructuralHOne318.projection R c)
  infer_instance
lemma flat [Flat (finiteProjection R c D)] [Flat (infinityProjection R c D)] : Flat (projection R c D) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (SchemeOpenPushout318.cover (ContactProjectiveQuotientOverlap318.finiteMap R c D)
      (ContactProjectiveQuotientOverlap318.infinityMap R c D))
  intro b
  cases b with
  | false => change Flat (finiteChart R c D ≫ projection R c D); rw [finite_projection]; infer_instance
  | true => change Flat (infinityChart R c D ≫ projection R c D); rw [infinity_projection]; infer_instance
lemma locallyQuasiFinite [LocallyQuasiFinite (finiteProjection R c D)]
    [LocallyQuasiFinite (infinityProjection R c D)] : LocallyQuasiFinite (projection R c D) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyQuasiFinite)
    (SchemeOpenPushout318.cover (ContactProjectiveQuotientOverlap318.finiteMap R c D)
      (ContactProjectiveQuotientOverlap318.infinityMap R c D))
  intro b
  cases b with
  | false => change LocallyQuasiFinite (finiteChart R c D ≫ projection R c D); rw [finite_projection]; infer_instance
  | true => change LocallyQuasiFinite (infinityChart R c D ≫ projection R c D); rw [infinity_projection]; infer_instance
/-- Correct finite-flat criterion: local flatness and local quasi-finiteness,
combined with the actual global projective properness. Local finiteness is
not imposed on the open chart restrictions. -/
lemma finite_flat [Flat (finiteProjection R c D)] [Flat (infinityProjection R c D)]
    [LocallyQuasiFinite (finiteProjection R c D)] [LocallyQuasiFinite (infinityProjection R c D)] :
    IsFinite (projection R c D) ∧ Flat (projection R c D) := by
  letI := locallyQuasiFinite R c D
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _,flat R c D⟩
end ContactProjectiveQuotientProperties318
