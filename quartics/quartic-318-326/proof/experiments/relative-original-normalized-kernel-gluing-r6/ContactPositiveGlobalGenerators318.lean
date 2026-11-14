module
public import FiniteLaurentSectionExtension318
public import ContactTwistGlobalCoordinates318
public section
noncomputable section
namespace ContactPositiveGlobalGenerators318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open ContactTwistGlobalCoordinates318
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Module (LaurentPolynomial R) (originalSections R c L) := overlapLaurentModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance (d : ℤ) : Module R Γ((twist R c L d).object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R
    (ContactRelativeStructuralHOne318.projection R c) (twist R c L d) ⊤

/-- Produce a finite family of GENUINE original global sections whose
finite-chart untwisted values are the complete original polynomial-chart
generators, at every sufficiently large twist. -/
theorem finite_generators : ∃ N r : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Fin r → Γ((twist R c L (n : ℤ)).object,⊤),
      Submodule.span (Polynomial R) (Set.range (fun i => finiteValue R c L n (s i))) = ⊤ := by
  obtain ⟨r,g,hg⟩ := Module.Finite.exists_fin (R := Polynomial R) (M := finiteSections R c L)
  obtain ⟨N,hN⟩ := FiniteLaurentSectionExtension318.negative R (originalSections R c L)
    (fun i => ContactOriginalRelativeOverlapSpan318.finiteMap R c L (g i))
    (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).range
    (RelativePolynomialChartBound318.negative_stable R (originalSections R c L)
      (infinitySections R c L) (ContactOriginalRelativeOverlapSpan318.infinityMap R c L)
      (infinity_polynomial R c L)) (ContactOriginalRelativeOverlapSpan318.infinity_span R c L)
  refine ⟨N,r,fun n hn => ?_⟩
  have hb : ∀ i, ∃ b : infinitySections R c L,
      ContactOriginalRelativeOverlapSpan318.infinityMap R c L b =
        (T (-(n : ℤ)) : LaurentPolynomial R) •
          ContactOriginalRelativeOverlapSpan318.finiteMap R c L (g i) := fun i => hN n hn i
  choose b hb using hb
  have hs : ∀ i, ∃ s : Γ((twist R c L (n : ℤ)).object,⊤),
      finiteValue R c L n s = g i ∧ infinityValue R c L n s = b i := by
    intro i
    apply exists_global R c L n (g i) (b i)
    rw [hb]
    change _ = (T (n : ℤ) : LaurentPolynomial R) •
      ((T (-(n : ℤ)) : LaurentPolynomial R) • _)
    rw [smul_smul,← T_add,add_neg_cancel,T_zero,one_smul]
  choose s hs using hs
  refine ⟨s,?_⟩
  have he : (fun i => finiteValue R c L n (s i)) = g := funext (fun i => (hs i).1)
  rw [he]
  exact hg

/-- The infinity generators are produced separately with the opposite
Laurent sign. They live in the same original twist at the same index. -/
theorem infinity_generators : ∃ N r : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Fin r → Γ((twist R c L (n : ℤ)).object,⊤),
      Submodule.span (Polynomial R) (Set.range (fun i => infinityValue R c L n (s i))) = ⊤ := by
  obtain ⟨r,g,hg⟩ := Module.Finite.exists_fin (R := Polynomial R) (M := infinitySections R c L)
  obtain ⟨N,hN⟩ := FiniteLaurentSectionExtension318.positive R (originalSections R c L)
    (fun i => ContactOriginalRelativeOverlapSpan318.infinityMap R c L (g i))
    (ContactOriginalRelativeOverlapSpan318.finiteMap R c L).range
    (RelativePolynomialChartGenerators318.positive_stable R (originalSections R c L)
      (finiteSections R c L) (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
      (finite_polynomial R c L)) (ContactOriginalRelativeOverlapSpan318.finite_span R c L)
  refine ⟨N,r,fun n hn => ?_⟩
  have ha : ∀ i, ∃ a : finiteSections R c L,
      ContactOriginalRelativeOverlapSpan318.finiteMap R c L a =
        (T (n : ℤ) : LaurentPolynomial R) •
          ContactOriginalRelativeOverlapSpan318.infinityMap R c L (g i) := fun i => hN n hn i
  choose a ha using ha
  have hs : ∀ i, ∃ s : Γ((twist R c L (n : ℤ)).object,⊤),
      finiteValue R c L n s = a i ∧ infinityValue R c L n s = g i :=
    fun i => exists_global R c L n (a i) (g i) (ha i)
  choose s hs using hs
  refine ⟨s,?_⟩
  have he : (fun i => infinityValue R c L n (s i)) = g := funext (fun i => (hs i).2)
  rw [he]
  exact hg

/-- ONE internally produced positive bound supplies H1 vanishing and
actual finite global generating families on BOTH whole original charts.
No reducedness, field, free-line or preselected generator is assumed. -/
theorem exists_uniform_bound : ∃ N r q : ℕ, ∀ n : ℕ, N ≤ n →
    (∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n : ℤ)),x=0) ∧
    (∃ s : Fin r → Γ((twist R c L (n : ℤ)).object,⊤),
      Submodule.span (Polynomial R) (Set.range (fun i => finiteValue R c L n (s i))) = ⊤) ∧
    (∃ s : Fin q → Γ((twist R c L (n : ℤ)).object,⊤),
      Submodule.span (Polynomial R) (Set.range (fun i => infinityValue R c L n (s i))) = ⊤) := by
  obtain ⟨A,r,hA⟩ := finite_generators R c L
  obtain ⟨B,q,hB⟩ := infinity_generators R c L
  obtain ⟨C,hC⟩ := ContactRelativeGeometricVanishing318.exists_bound R c L
  refine ⟨max A (max B C),r,q,fun n hn => ?_⟩
  have hAn : A ≤ n := (le_max_left _ _).trans hn
  have hBn : B ≤ n := (le_max_left B C).trans ((le_max_right A _).trans hn)
  have hCn : C ≤ n := (le_max_right B C).trans ((le_max_right A _).trans hn)
  exact ⟨hC n hCn,hA n hAn,hB n hBn⟩
end ContactPositiveGlobalGenerators318
