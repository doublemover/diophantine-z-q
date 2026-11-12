module
public import ContactNormalizedBoundedAbel318
public section
noncomputable section
namespace ContactPositiveBoundedPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
open RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (n : ℕ) (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n:ℤ)),x=0)
local notation "p" => ContactRelativeStructuralHOne318.projection R c
local notation "b" => ContactNormalizedSectionParameter318.projection R c (twist R c L n) hz
local notation "D" => ContactNormalizedBoundedDivisor318.line R c (twist R c L n) hz
@[expose] def translatedClass := value p b (OriginalLineAbelTransformation318.point p b D) *
  (value p b (original p b (classOf (ContactPositiveAbelPresentation318.positiveLine R c n))))⁻¹
lemma translated_original : translatedClass R c L n hz=ContactPositiveAbelPresentation318.originalClass R c L n hz := by
  apply RelativeClassSheafProduct318.translated p b
  have he := ContactNormalizedBoundedAbel318.original_value R c (twist R c L n) hz
  rw [ContactPositiveAbelPresentation318.twist_class] at he
  exact he
/-- Every original line on every affine coefficient test has a genuine
fppf-local positive presentation through an ACTUAL bounded varying-divisor
parameter. The numerical bound and classifying map are produced from the
whole normalized family; neither is supplied as an assumed interface. -/
theorem exists_presentation : ∃ M : ℕ,∀ n : ℕ,M≤n →
    ∃ h : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n:ℤ)),x=0,
      Flat (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      Surjective (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      LocallyOfFinitePresentation (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      (∃ N : ℕ,Nonempty (ContactBoundedCartierEquiv318.Point c N
        (ContactNormalizedAbsoluteAmbient318.base R c (twist R c L n) h))) ∧
      translatedClass R c L n h=ContactPositiveAbelPresentation318.originalClass R c L n h := by
  obtain ⟨M,hM⟩ := ContactGeneratedPositiveFibers318.exists_bound R c L
  refine ⟨M,fun n hn => ?_⟩
  obtain ⟨h,hf,hs,hp⟩ := hM n hn
  exact ⟨h,hf,hs,hp,
    ⟨ContactNormalizedParameterCompact318.bound R c (twist R c L n) h,
      ⟨ContactNormalizedBoundedCartier318.point R c (twist R c L n) h⟩⟩,
    translated_original R c L n h⟩
end ContactPositiveBoundedPresentation318
