module
public import ContactGeneratedPositiveFibers318
public import ContactNormalizedAbelFiber318
public import RelativeClassSheafProduct318
public import ContactRelativeProjectivePositive318
public section
noncomputable section
namespace ContactPositiveAbelPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
open RelativeClassSheafPoint318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "p" => ContactRelativeStructuralHOne318.projection R c

/-- The positive correction is the actual power of the ORIGINAL contact
projective O(1), through its proved same-source comparison, not the j-map. -/
abbrev positiveLine (n : ℕ) :=
  LineSheafTensorPower318.line (ContactRelativeProjectivePositive318.line R c) n

lemma twist_class (n : ℕ) : classOf (twist R c L (n:ℤ))=
    classOf L * classOf (positiveLine R c n) := by
  have e := ContactRelativeProjectivePositive318.twistedPowerIso R c L n ≪≫
    ContactRelativeTwistPowers318.twistedPowerIso R c L n
  exact (classOf_eq e).symm

variable (n : ℕ) (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n:ℤ)),x=0)
local notation "b" => ContactNormalizedSectionParameter318.projection R c (twist R c L n) hz
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c (twist R c L n) hz

@[expose] def translatedClass :=
  value p b (OriginalLineAbelTransformation318.point p b D) *
    (value p b (original p b (classOf (positiveLine R c n))))⁻¹
@[expose] def originalClass := value p b (original p b (classOf L))

/-- The ACTUAL effective Cartier family, minus the actual original
positive projective twist, recovers the original arbitrary line class
in the relative fppf sheaf over the whole constructed parameter. -/
theorem translated_original : translatedClass R c L n hz=originalClass R c L n hz := by
  apply RelativeClassSheafProduct318.translated p b
  have h := ContactNormalizedAbelFiber318.original_sheaf_class R c (twist R c L n) hz
  rw [twist_class] at h
  exact h

/-- Every original relative line admits an internally constructed
sufficiently positive effective-divisor presentation on a genuine fppf
cover of its original coefficient base. The represented parameter and
actual global Cartier divisor already exist; this theorem does not
identify all varying-line fibers into a represented Picard/Jacobian. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ h : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n:ℤ)),x=0,
      Flat (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      Surjective (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      LocallyOfFinitePresentation
        (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      translatedClass R c L n h=originalClass R c L n h := by
  obtain ⟨N,hN⟩ := ContactGeneratedPositiveFibers318.exists_bound R c L
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨h,hf,hs,hp⟩ := hN n hn
  exact ⟨h,hf,hs,hp,translated_original R c L n h⟩
end ContactPositiveAbelPresentation318
