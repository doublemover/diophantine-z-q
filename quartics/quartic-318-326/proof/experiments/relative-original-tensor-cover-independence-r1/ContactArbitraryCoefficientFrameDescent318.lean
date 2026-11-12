module
public import RelativeFrameRecoveryBaseChange318
public section
noncomputable section
namespace ContactArbitraryCoefficientFrameDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactCanonicalCoefficientFrame318.projection R c
variable {S : Scheme.{0}} (b : S ⟶ Spec R) (F : RelativeFamilyFrameRule318.Rule p L)
/-- Concrete original Contact consumer: the entire original coefficient
curve over ANY new scheme carries the genuinely descended full frame,
with the exact native pullback equality, including nonaffine coefficients. -/
lemma recovery :
    RelativeFamilyFrameRecovery318.frame (pullback.snd p b)
      (LineSheafPullback318.line (pullback.fst p b) L)
      (RelativeFrameRuleBaseChange318.rule p L b F)=
    OriginalFramePullback318.frame (pullback.fst p b) L
      (RelativeFamilyFrameRecovery318.frame p L F) :=
  RelativeFrameRecoveryBaseChange318.recovery p L b F
/-- The actual canonical affine parameter can now be compared with an
iterated original coefficient family by a two-sided FULL-frame equivalence.
This does not assert that the Picard quotient is represented. -/
@[expose] def affineParameter
    (A : CommRingCat.{0}) [Algebra ℚ A] (f : R →ₐ[ℚ] A)
    (a : Spec A ⟶ S) (ha : a ≫ b=ContactCanonicalCoefficientFrame318.base R A f) :
    ContactTrivializationAffinePoints318.Points R c L A f ≃
      Frames (LineSheafPullback318.line (pullback.fst (pullback.snd p b) a)
        (LineSheafPullback318.line (pullback.fst p b) L)) := by
  have he : Frames (ContactCanonicalCoefficientFrame318.line R A f c L)=
      Frames (IteratedCoefficientFrameEquivalence318.directLine p L b a) := by
    change Frames (LineSheafPullback318.line
      (pullback.fst p (ContactCanonicalCoefficientFrame318.base R A f)) L)=
      Frames (LineSheafPullback318.line (pullback.fst p (a ≫ b)) L)
    rw [ha]
  exact (ContactCanonicalTrivializationParameter318.equivalence R c L A f).trans
    ((Equiv.cast he).trans (IteratedCoefficientFrameEquivalence318.equivalence p L b a).symm)
end ContactArbitraryCoefficientFrameDescent318
