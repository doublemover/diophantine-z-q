module
public import ContactPositiveDifferenceTwists318
public section
noncomputable section
namespace ContactPositiveDifferenceCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactPositiveDifferenceTwists318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
/-- A SINGLE internally chosen positive index produces TWO actual
normalized Cartier families whose common parameter is a genuine fppf
cover. Both bounds, families and covering properties are constructed. -/
theorem exists_cover : ∃ n : ℕ,
    ∃ hA : ∀ x : NonreducedLineMayerVietoris318.H1 (numerator R c L n),x=0,
    ∃ hB : ∀ x : NonreducedLineMayerVietoris318.H1 (denominator R c n),x=0,
      Flat (ContactNormalizedPairData318.projection R c (numerator R c L n) (denominator R c n) hA hB) ∧
      Surjective (ContactNormalizedPairData318.projection R c (numerator R c L n) (denominator R c n) hA hB) ∧
      LocallyOfFinitePresentation (ContactNormalizedPairData318.projection R c (numerator R c L n) (denominator R c n) hA hB) := by
  obtain ⟨m,hm⟩ := ContactGeneratedPositiveFibers318.exists_bound R c L
  obtain ⟨k,hk⟩ := ContactGeneratedPositiveFibers318.exists_bound R c (unitLine R c)
  obtain ⟨hA,hAf,hAs,hAp⟩ := hm (max m k) (le_max_left _ _)
  obtain ⟨hB,hBf,hBs,hBp⟩ := hk (max m k) (le_max_right _ _)
  letI := hAf
  letI := hAs
  letI := hAp
  letI := hBf
  letI := hBs
  letI := hBp
  exact ⟨max m k,hA,hB,inferInstance,inferInstance,inferInstance⟩
end ContactPositiveDifferenceCover318
