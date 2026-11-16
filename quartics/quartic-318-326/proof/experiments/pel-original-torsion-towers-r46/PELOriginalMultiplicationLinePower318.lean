module
public import PELOriginalPolarizationQuadraticPower318
public section
noncomputable section
namespace PELOriginalMultiplicationLinePower318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalCubeTestClasses318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalIntegerMultiplication318
open PELOriginalPolarizationQuadraticPower318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The literal constant zero-map line on the original scheme. -/
@[expose] def zeroLine : Line (candidate τ hτ) :=
  LineSheafPullback318.line (0 : Points τ hτ _ (π τ hτ)).val (line τ hτ)
/-- Actual zero-normalized original line. No choice of trivialization
of a line over Spec(C) is hidden in this definition. -/
@[expose] def normalizedLine : Line (candidate τ hτ) :=
  LineSheafTensor318.line (line τ hτ) (FramedLineInverse318.inverse (zeroLine τ hτ))
lemma normalized_class : classOf (normalizedLine τ hτ)=
    q τ hτ (π τ hτ) (identityPoint τ hτ) := by
  rw [normalizedLine,LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse]
  change _=LineClassPullbackHom318.pullback (𝟙 _) _*(classOf (zeroLine τ hτ))⁻¹
  rw [LineClassPullbackHom318.identity]
  rfl
lemma pull_zero_class (n : ℤ) :
    LineClassPullbackHom318.pullback (multiplication τ hτ n) (classOf (zeroLine τ hτ))=
      classOf (zeroLine τ hτ) := by
  have h := PELOriginalNormalizedPolarizationFamily318.value_pull τ hτ (π τ hτ)
    (multiplication τ hτ n) (over_complex τ hτ n) (0 : Points τ hτ _ (π τ hτ))
  simpa only [map_zero] using h
lemma normalized_pull_class (n : ℤ) :
    classOf (LineSheafPullback318.line (multiplication τ hτ n) (normalizedLine τ hτ))=
      (classOf (normalizedLine τ hτ))^(n.natAbs*n.natAbs) := by
  change LineClassPullbackHom318.pullback (multiplication τ hτ n)
    (classOf (normalizedLine τ hτ))=_
  rw [normalized_class]
  change LineClassPullbackHom318.pullback (multiplication τ hτ n)
    (value τ hτ (π τ hτ) (identityPoint τ hτ)*(value τ hτ (π τ hτ) 0)⁻¹)=_
  rw [map_mul,map_inv,
    PELOriginalNormalizedPolarizationFamily318.value_pull τ hτ _ _ (over_complex τ hτ n),
    PELOriginalNormalizedPolarizationFamily318.value_pull τ hτ _ _ (over_complex τ hτ n),map_zero]
  have hp : pull τ hτ (π τ hτ) (multiplication τ hτ n) (over_complex τ hτ n)
      (identityPoint τ hτ)=n • identityPoint τ hτ := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [hp]
  exact q_zsmul τ hτ (π τ hτ) (identityPoint τ hτ) n

/-- Genuine algebraic integer-square power law for the normalized SAME
line, as a whole sheaf isomorphism, including n=0 and negative integers. -/
@[expose] def powerIso (n : ℤ) :
    (LineSheafPullback318.line (multiplication τ hτ n) (normalizedLine τ hτ)).object ≅
      (LineSheafTensorPower318.line (normalizedLine τ hτ) (n.natAbs*n.natAbs)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafTensorPower318.classOf_power,normalized_pull_class]

/-- Exact original-line version: the zero-map line is explicitly
retained. This avoids assuming a canonical normalization of its fiber. -/
@[expose] def originalPowerIso (n : ℤ) :
    (LineSheafPullback318.line (multiplication τ hτ n) (line τ hτ)).object ≅
      (LineSheafTensor318.line
        (LineSheafTensorPower318.line (normalizedLine τ hτ) (n.natAbs*n.natAbs))
        (zeroLine τ hτ)).object := by
  apply Classical.choice
  apply (classOf_eq_iff _ _).mp
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafTensorPower318.classOf_power]
  have h := normalized_pull_class τ hτ n
  change LineClassPullbackHom318.pullback (multiplication τ hτ n)
    (classOf (normalizedLine τ hτ))=_ at h
  rw [normalizedLine,LineSheafClassGroup318.classOf_tensor,
    LineSheafClassGroup318.classOf_inverse,map_mul,map_inv,pull_zero_class] at h
  change LineClassPullbackHom318.pullback (multiplication τ hτ n) (classOf (line τ hτ))=_
  calc
    _ = (LineClassPullbackHom318.pullback (multiplication τ hτ n) (classOf (line τ hτ))*
      (classOf (zeroLine τ hτ))⁻¹)*classOf (zeroLine τ hτ) := by group
    _ = _ := by rw [h]
end PELOriginalMultiplicationLinePower318
