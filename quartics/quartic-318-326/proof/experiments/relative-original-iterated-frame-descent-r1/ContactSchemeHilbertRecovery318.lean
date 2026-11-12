module
public import ContactSchemeHilbertLocalRecovery318
public section
noncomputable section
namespace ContactSchemeHilbertRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactSchemeHilbertData318.Data c n b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "U" => RelativeAffineTestCover318.cover ℚ b
local notation "f" => ContactSchemeHilbertLocalRecovery318.point c n b D
local notation "q" => D.ideal.subschemeι
local notation "r" => ContactSchemePointFamily318.into c n b f
/-- Shared complete original closed models on the whole affine base
cover, now for an arbitrary coefficient SCHEME. -/
@[expose] def models : SchemeClosedFamilyLocalModels318.Data (pullback.snd p b) q r where
  family i := (ContactSchemeHilbertTest318.data c n b D (RelativeAffineTestCover318.ring ℚ b i)
    (RelativeAffineTestCover318.point ℚ b i)).val.ideal.subscheme
  projection i := ContactSchemeHilbertTest318.projection c n b D (RelativeAffineTestCover318.ring ℚ b i)
    (RelativeAffineTestCover318.point ℚ b i)
  left i := ContactSchemeHilbertTest318.toFamily c n b D (RelativeAffineTestCover318.ring ℚ b i)
    (RelativeAffineTestCover318.point ℚ b i)
  right := ContactSchemeHilbertLocalRecovery318.map c n b D
  left_cartesian i := ContactSchemeHilbertTest318.cartesian c n b D (RelativeAffineTestCover318.ring ℚ b i)
    (RelativeAffineTestCover318.point ℚ b i)
  right_cartesian i := (ContactSchemeHilbertLocalRecovery318.cartesian c n b D i).paste_vert
    (RelativeSchemeCoefficient318.cartesian p b
      (VaryingSourceCoefficientPullback318.base ℚ (RelativeAffineTestCover318.ring ℚ b i))
      (U.f i) (RelativeAffineTestCover318.over ℚ b i))
  over_source i := (ContactSchemeHilbertTest318.source_cartesian c n b D (RelativeAffineTestCover318.ring ℚ b i)
    (RelativeAffineTestCover318.point ℚ b i)).w.trans (ContactSchemeHilbertLocalRecovery318.source c n b D i).symm
/-- The WHOLE original standard family over ANY coefficient scheme is
recovered by the actual global universal fiber, preserving its source. -/
@[expose] def comparison : D.ideal.subscheme ≅ ContactSchemePointFamily318.family c n b f :=
  SchemeClosedFamilyLocalModels318.iso (pullback.snd p b) q r (models c n b D)
@[reassoc] lemma comparison_source : (comparison c n b D).hom ≫ r=q :=
  SchemeClosedFamilyLocalModels318.iso_into _ _ _ _
lemma ideal_recovery : (ContactSchemePointFamily318.extract c n b f).ideal=D.ideal := by
  have h := Scheme.Hom.ker_comp_of_isIso (comparison c n b D).hom r
  have he := congrArg (fun k : D.ideal.subscheme ⟶ pullback p b => k.ker) (comparison_source c n b D)
  exact (h.symm.trans he).trans D.ideal.ker_subschemeι
end ContactSchemeHilbertRecovery318
