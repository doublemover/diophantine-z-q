module
public import ContactZeroOverlapJointMono318
public section
noncomputable section
namespace ContactZeroIntersectionLegs318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "P" => Γ(L.object,⊤)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "inc" => ContactNormalizedZeroTransitions318.inclusion R c L hz
local notation "proj" => ContactNormalizedZeroTransitions318.projection R c L hz
local notation "fp" => ContactLiteralTripleFamilyRotation318.projection R c L hz
local notation "e" => ContactLiteralTripleZeroFamily318.intersectionIso R c L hz
local notation "first" => ProjectiveParameterSliceTriplePullback318.first R P
local notation "second" => ProjectiveParameterSliceTriplePullback318.second R P
local notation "chart" => ContactNormalizedOriginalCurve318.chart R c L hz
variable (i j k : Fin F.size)

/-- Both base-overlap legs of the ACTUAL triple intersection comparison
are retained, with the exact literal iterated-localization projections. -/
@[reassoc] lemma first_leg : (e i j k).hom ≫ fp i j k ≫ first i j k=
    pullback.fst (inc i j) (inc i k) ≫ proj i j := by
  simp only [ContactLiteralTripleZeroFamily318.intersectionIso,
    ContactNormalizedZeroIntersection318.iso,
    ContactLiteralTripleFamilyRotation318.projection,ContactNormalizedZeroTransitions318.projection,
    Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullback.congrHom_hom,pullback.lift_snd_assoc]
  rw [← ProjectiveParameterSliceTriplePullback318.comparison_fst,
    PullbackBaseIso318.inv_snd_assoc,Iso.inv_hom_id_assoc,
    PullbackOverlapIntersection318.hom_first]
@[reassoc] lemma second_leg : (e i j k).hom ≫ fp i j k ≫ second i j k=
    pullback.snd (inc i j) (inc i k) ≫ proj i k := by
  simp only [ContactLiteralTripleZeroFamily318.intersectionIso,
    ContactNormalizedZeroIntersection318.iso,
    ContactLiteralTripleFamilyRotation318.projection,ContactNormalizedZeroTransitions318.projection,
    Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullback.congrHom_hom,pullback.lift_snd_assoc]
  rw [← ProjectiveParameterSliceTriplePullback318.comparison_snd,
    PullbackBaseIso318.inv_snd_assoc,Iso.inv_hom_id_assoc,
    PullbackOverlapIntersection318.hom_second]
@[reassoc] lemma inverse_second : (e i j k).inv ≫
    pullback.snd (inc i j) (inc i k) ≫ proj i k=fp i j k ≫ second i j k := by
  rw [← second_leg R c L hz i j k,Iso.inv_hom_id_assoc]

local notation "orig" => ContactNormalizedFamilyJointMono318.original R c L hz
  (ContactLiteralTripleZeroFamily318.ring R c L hz i j k)
  (ContactLiteralTripleZeroFamily318.coefficient R c L hz i j k)
  (ProjectiveParameterSliceTripleAlgebra318.universal R P i j k)
@[reassoc] lemma original : (e i j k).hom ≫ orig=
    pullback.fst (inc i j) (inc i k) ≫ inc i j ≫ chart i := by
  rw [ContactNormalizedFamilyJointMono318.original,
    ContactLiteralTripleZeroFamily318.intersectionIso,Iso.trans_hom,Category.assoc,
    pullback.congrHom_hom,pullback.lift_fst_assoc,
    ContactNormalizedZeroIntersection318.iso_original_assoc]
@[reassoc] lemma inverse_original_second : (e i j k).inv ≫
    pullback.snd (inc i j) (inc i k) ≫ inc i k ≫ chart i=orig := by
  rw [← pullback.condition_assoc,← original R c L hz i j k,Iso.inv_hom_id_assoc]
end ContactZeroIntersectionLegs318
