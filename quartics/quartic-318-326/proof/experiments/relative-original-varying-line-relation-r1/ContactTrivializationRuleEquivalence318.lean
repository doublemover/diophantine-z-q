module
public import AffineFrameRulePullback318
public import ContactTrivializationActualDescent318
public section
noncomputable section
namespace ContactTrivializationRuleEquivalence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local notation "N" => L' R S f c L
/-- SAME trivialization-open points classify natural FULL frame data on
ALL affine scheme tests of the original coefficient curve, not just its
chosen two charts. The coefficient base S remains affine in this statement. -/
@[expose] def equivalence : ContactTrivializationAffinePoints318.Points R c L S f ≃
    AffineFrameRule318.Rule N :=
  (ContactTrivializationAffinePoints318.equivalence R c L S f).trans
    (AffineFrameRuleEquivalence318.equivalence N)
lemma actual_test (x : ContactTrivializationAffinePoints318.Points R c L S f)
    (T : CommRingCat.{0}) (t : Spec T ⟶ curve S c) :
    (equivalence R c L S f x).app T t=
      OriginalFramePullback318.frame t N (ContactTrivializationAffinePoints318.equivalence R c L S f x) := rfl
lemma recover_original (F : AffineFrameRule318.Rule N) :
    ContactTrivializationAffinePoints318.equivalence R c L S f
      ((equivalence R c L S f).symm F)=(AffineFrameRuleEquivalence318.equivalence N).symm F :=
  (ContactTrivializationAffinePoints318.equivalence R c L S f).apply_symm_apply _
end ContactTrivializationRuleEquivalence318
