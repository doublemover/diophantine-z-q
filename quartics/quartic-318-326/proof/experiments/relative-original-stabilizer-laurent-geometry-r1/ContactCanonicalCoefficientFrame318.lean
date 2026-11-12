module
public import OriginalFrameModelNaturality318
public import RelativeCoefficientCartesian318
public import ContactTrivializationFullNaturality318
public section
noncomputable section
namespace ContactCanonicalCoefficientFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
abbrev projection := ContactRelativeLinearOpenChart318.projection R c
abbrev base := Spec.map (CommRingCat.ofHom f.toRingHom)
abbrev original := ContactRelativeCoefficientChange318.curveMap R S f c
lemma cartesian : IsPullback (original R S f c) (ContactRelativeLinearOpenChart318.projection S c)
    (projection R c) (base R S f) :=
  RelativeCoefficientCartesian318.cartesian (CommRingCat.of ℚ) R S f
    (ContactIntrinsicDifferentials318.structureMap c)
abbrev family := pullback (projection R c) (base R S f)
abbrev line := LineSheafPullback318.line (pullback.fst (projection R c) (base R S f)) L
abbrev model : curve S c ≅ family R S f c := (cartesian R S f c).isoPullback
/-- SAME original coefficient line versus its literal relative pullback
family. This is a two-sided full-frame equivalence, not a class comparison. -/
@[expose] def equivalence : Frames (line R S f c L) ≃ Frames (L' R S f c L) :=
  CartesianFrameModelEquivalence318.equivalence L (original R S f c)
    (ContactRelativeLinearOpenChart318.projection S c) (projection R c) (base R S f)
    (cartesian R S f c)
lemma forward (a : Frames (line R S f c L)) :
    equivalence R S f c L a=OriginalFramePathTransport318.transport L (model R S f c).hom
      (pullback.fst (projection R c) (base R S f)) (original R S f c)
      (cartesian R S f c).isoPullback_hom_fst a := rfl
end ContactCanonicalCoefficientFrame318
