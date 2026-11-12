module
public import ContactCanonicalCoefficientNaturality318
public section
noncomputable section
namespace ContactCanonicalTrivializationParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
/-- The SAME original open parameter represents full frames of the
LITERAL p-first coefficient pullback family, with both inverse maps. -/
@[expose] def equivalence : ContactTrivializationAffinePoints318.Points R c L S f ≃
    Frames (ContactCanonicalCoefficientFrame318.line R S f c L) :=
  (ContactTrivializationAffinePoints318.equivalence R c L S f).trans
    (ContactCanonicalCoefficientFrame318.equivalence R S f c L).symm
lemma original_frame (x : ContactTrivializationAffinePoints318.Points R c L S f) :
    ContactCanonicalCoefficientFrame318.equivalence R S f c L (equivalence R c L S f x)=
      ContactTrivializationAffinePoints318.equivalence R c L S f x :=
  (ContactCanonicalCoefficientFrame318.equivalence R S f c L).apply_symm_apply _
variable (T : CommRingCat.{0}) [Algebra ℚ T] (g : S →ₐ[ℚ] T)
local instance : Algebra R S := f.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local notation "U" => ContactArbitraryNowhereZeroOpen318.locus R c L
local notation "φ" => ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g
abbrev pointMap := AffineOpenPointNaturality318.map R
  (ContactArbitrarySectionParameter318.parameterRing R c L) S T U φ
/-- Whole coefficient naturality of that SAME parameter in the canonical
relative-family convention needed for arbitrary-base frame descent. -/
lemma natural (x : ContactTrivializationAffinePoints318.Points R c L S f) :
    OriginalFramePathTransport318.transport L (ContactCanonicalCoefficientNaturality318.coefficient R S T f g c)
      (pullback.fst (ContactCanonicalCoefficientFrame318.projection R c)
        (ContactCanonicalCoefficientFrame318.base R S f))
      (pullback.fst (ContactCanonicalCoefficientFrame318.projection R c)
        (ContactCanonicalCoefficientFrame318.base R T (g.comp f)))
      (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) (equivalence R c L S f x)=
    equivalence R c L T (g.comp f) (pointMap R c L S f T g x) := by
  apply (ContactCanonicalCoefficientFrame318.equivalence R T (g.comp f) c L).injective
  rw [ContactCanonicalCoefficientNaturality318.natural,original_frame,original_frame]
  exact ContactTrivializationFullNaturality318.natural R S T f g c L x
end ContactCanonicalTrivializationParameter318
