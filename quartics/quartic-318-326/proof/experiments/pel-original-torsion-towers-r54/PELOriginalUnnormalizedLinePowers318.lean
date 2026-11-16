module
public import FieldLineClassTrivial318
public import PELOriginalMultiplicationLinePower318
public section
noncomputable section
namespace PELOriginalUnnormalizedLinePowers318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalSchemePointGroup318
open PELOriginalIntegerMultiplication318 PELOriginalMultiplicationLinePower318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The original zero-map line is genuinely trivial because its
actual fiber over Spec(C) has a global frame. The frame is chosen;
no canonical normalization of its value is asserted. -/
lemma zeroLine_class : classOf (zeroLine τ hτ)=1 := by
  change LineClassPullbackHom318.pullback
    ((π τ hτ)≫PELOriginalSchemeAdditionOperations318.zeroPoint τ hτ) (classOf (line τ hτ))=1
  rw [LineClassPullbackLaws318.pullback_composition]
  have h : LineClassPullbackHom318.pullback (PELOriginalSchemeAdditionOperations318.zeroPoint τ hτ)
      (classOf (line τ hτ))=1 :=
    FieldLineClassTrivial318.classOf_eq_one ℂ
      (LineSheafPullback318.line (PELOriginalSchemeAdditionOperations318.zeroPoint τ hτ) (line τ hτ))
  rw [h,map_one]
@[expose] def zeroLineIso : (zeroLine τ hτ).object ≅
    SheafOfModules.unit (candidate τ hτ).ringCatSheaf :=
  Classical.choice ((LineSheafUnit318.eq_unitClass_iff _).mp (zeroLine_class τ hτ))
lemma normalized_eq : classOf (PELOriginalMultiplicationLinePower318.normalizedLine τ hτ)=
    classOf (line τ hτ) := by
  rw [PELOriginalMultiplicationLinePower318.normalizedLine,
    LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,
    zeroLine_class,inv_one,mul_one]
@[expose] def normalizationIso : (PELOriginalMultiplicationLinePower318.normalizedLine τ hτ).object ≅
    (line τ hτ).object := Classical.choice ((classOf_eq_iff _ _).mp (normalized_eq τ hτ))

/-- The familiar integer-square polarization identity is now proved
for the SAME unnormalized original algebraic line, with the missing
field-line triviality produced rather than assumed. -/
lemma multiplication_class (n : ℤ) :
    classOf (LineSheafPullback318.line (multiplication τ hτ n) (line τ hτ))=
      (classOf (line τ hτ))^(n.natAbs*n.natAbs) := by
  have h := normalized_pull_class τ hτ n
  change LineClassPullbackHom318.pullback (multiplication τ hτ n)
    (classOf (PELOriginalMultiplicationLinePower318.normalizedLine τ hτ))=_ at h
  rw [normalized_eq] at h
  exact h
@[expose] def multiplicationIso (n : ℤ) :
    (LineSheafPullback318.line (multiplication τ hτ n) (line τ hτ)).object ≅
      (LineSheafTensorPower318.line (line τ hτ) (n.natAbs*n.natAbs)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafTensorPower318.classOf_power,multiplication_class]

/-- BOTH inverse maps remain actual sheaf maps after every arbitrary
scheme base change. No degree, finiteness or etaleness is deduced here. -/
@[expose] def testIso {Y : Scheme} (f : Y ⟶ candidate τ hτ) (n : ℤ) :=
  (Scheme.Modules.pullback f).mapIso (multiplicationIso τ hτ n)
lemma test_hom_inv {Y : Scheme} (f : Y ⟶ candidate τ hτ) (n : ℤ) :
    (testIso τ hτ f n).hom≫(testIso τ hτ f n).inv=𝟙 _ := (testIso τ hτ f n).hom_inv_id
end PELOriginalUnnormalizedLinePowers318
