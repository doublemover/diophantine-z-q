module
public import ContactSchemeHilbertData318
public section
noncomputable section
namespace ContactSchemeHilbertTest318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactSchemeHilbertData318.Data c n b) (S : CommRingCat.{0}) [Algebra ℚ S]
  (x : RelativeAffineTestRule318.Test ℚ b S)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
abbrev sourceMap := RelativeSchemeCoefficient318.map p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property
abbrev ideal := D.ideal.comap (sourceMap c b S x)
abbrev toFamily := IdealSheafCoefficientCartesian318.map D.ideal (sourceMap c b S x)
abbrev projection := (ideal c n b D S x).subschemeι ≫ ContactRelativeLinearOpenChart318.projection S c
lemma source_cartesian : IsPullback (toFamily c n b D S x) (ideal c n b D S x).subschemeι
    D.ideal.subschemeι (sourceMap c b S x) := IdealSheafCoefficientCartesian318.cartesian _ _
lemma cartesian : IsPullback (toFamily c n b D S x) (projection c n b D S x)
    (ContactSchemeHilbertData318.projection c n b D) x.val :=
  (source_cartesian c n b D S x).paste_vert
    (RelativeSchemeCoefficient318.cartesian p b (VaryingSourceCoefficientPullback318.base ℚ S) x.val x.property)
instance finite : IsFinite (projection c n b D S x) :=
  MorphismProperty.of_isPullback (cartesian c n b D S x) inferInstance
instance flat : Flat (projection c n b D S x) :=
  MorphismProperty.of_isPullback (cartesian c n b D S x) inferInstance
instance presentation : LocallyOfFinitePresentation (projection c n b D S x) :=
  MorphismProperty.of_isPullback (cartesian c n b D S x) inferInstance
lemma rank (y : PrimeSpectrum S) : (projection c n b D S x).finrank y=n := by
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian c n b D S x)]
  exact D.rank _
/-- Every affine coefficient test produces the literal full ideal comap
with DERIVED standard finite-flat/FP and rank conditions. -/
@[expose] def data : ContactHilbertData318.FixedRank S c n :=
  ⟨{ideal := ideal c n b D S x,finite := finite c n b D S x,flat := flat c n b D S x,
    presentation := presentation c n b D S x},rank c n b D S x⟩
end ContactSchemeHilbertTest318
