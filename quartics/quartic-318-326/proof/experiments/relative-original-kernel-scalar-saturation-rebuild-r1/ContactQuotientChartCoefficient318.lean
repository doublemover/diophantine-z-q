module
public import ContactQuotientSourceSupport318
public import RelativeCoefficientCartesian318
public section
noncomputable section
namespace ContactQuotientChartCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientChartTransfer318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (a : Chart) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) (n : ℕ) (I : Ideal c a S n)
abbrev extended : Ideal c a T n := VaryingProjectiveQuotientNaturality318.mapIdeal ℚ (ring c a) (Fin n) S T φ I
abbrev map : family c a T n (extended c a S T φ n I) ⟶ family c a S n I :=
  VaryingWholeIdealFamily318.map ℚ (ring c a) S I.val T φ
@[reassoc] lemma map_quotient : map c a S T φ n I ≫ quotientInto c a S n I=
    quotientInto c a T n (extended c a S T φ n I) ≫
      VaryingSourceCoefficientPullback318.sourceChange ℚ (ring c a) S T φ :=
  VaryingWholeIdealFamily318.map_into ℚ (ring c a) S I.val T φ
lemma cartesian : IsPullback (map c a S T φ n I) (projection c a T n (extended c a S T φ n I))
    (projection c a S n I) (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  VaryingWholeIdealFamily318.cartesian ℚ (ring c a) S I.val T φ
@[reassoc] lemma map_source : map c a S T φ n I ≫ ContactQuotientSourceSupport318.source c a S n I=
    ContactQuotientSourceSupport318.source c a T n (extended c a S T φ n I) := by
  change map c a S T φ n I ≫ (quotientInto c a S n I ≫
    VaryingSourceCoefficientPullback318.original ℚ (ring c a) S ≫ original c a)=_
  rw [← Category.assoc,map_quotient,Category.assoc,VaryingSourceCoefficientPullback318.source_original_assoc]
  rfl
@[reassoc] lemma map_projective : map c a S T φ n I ≫ projectiveInto c a S n I=
    projectiveInto c a T n (extended c a S T φ n I) ≫
      RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ
        (ContactIntrinsicDifferentials318.structureMap c) := by
  change map c a S T φ n I ≫ (quotientInto c a S n I ≫ into c a S)=_
  rw [← Category.assoc,map_quotient,Category.assoc]
  have hs := RelativeCoefficientChange318.into_square (CommRingCat.of ℚ) S T (ring c a) φ
    (ContactIntrinsicDifferentials318.structureMap c) (original c a)
    (ContactOriginalLinearOpenChart318.affine_over c a.form a.homogeneous)
  change quotientInto c a T n (extended c a S T φ n I) ≫
      (Spec.map (RelativeCoefficientChange318.ringMap (CommRingCat.of ℚ) S T (ring c a) φ) ≫ into c a S)=_
  rw [hs,← Category.assoc]
  rfl
/-- Whole support in a second original source chart survives arbitrary
coefficient extension, including nonflat and nilpotent ring maps. -/
lemma supported (b : Chart) (h : Supported c a b S n I) :
    Supported c a b T n (extended c a S T φ n I) := by
  apply (ContactQuotientSourceSupport318.supported_iff c a b T n _).mpr
  intro z
  have hz := (ContactQuotientSourceSupport318.supported_iff c a b S n I).mp h (map c a S T φ n I z)
  change (map c a S T φ n I ≫ ContactQuotientSourceSupport318.source c a S n I) z∈_ at hz
  rw [map_source] at hz
  exact hz
end ContactQuotientChartCoefficient318
