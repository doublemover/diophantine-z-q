module
public import ContactRelativeKernelCoefficientMaps318
public import RelativePolynomialChartFinite318
public import ContactRelativeChartFinitePresentation318
public section
noncomputable section
namespace ContactRelativeFiniteRelationQuotient318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeGeometricTwist318 ContactRelativeGlobalSectionLifting318
open ContactRelativeGeneratorPresentations318 ContactRelativeKernelCoefficientMaps318
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (n : ℕ) {ι : Type} (g : ι → Γ((twist R c L (n : ℤ)).object,⊤))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (finiteKernel R c L n g) := Module.compHom _ Polynomial.C
local instance : Module R (infinityKernel R c L n g) := Module.compHom _ Polynomial.C
local instance : Module R (overlapKernel R c L n g) :=
  RelativeLaurentScalar318.coefficientModule R _

/-- The literal coefficient relation boundary, with the source O(-n)
shift on its original reciprocal chart. Both images live in ONE kernel. -/
@[expose] def boundary : Submodule R (overlapKernel R c L n g) :=
  (finiteMap R c L n g).range ⊔ (infinityMap R c L n g).range

/-- The actual global-presentation relation quotient is finite over EVERY
coefficient ring R. Its positive polynomial kernel is finite because its
actual chart target is finitely PRESENTED. The Laurent spanning and scalar
actions of both original kernel maps were constructed, not hypothesized. -/
theorem finite [Finite ι]
    (hf : Function.Surjective (finiteEvaluation R c L n g))
    (hi : Function.Surjective (infinityEvaluation R c L n g)) :
    Module.Finite R ((overlapKernel R c L n g) ⧸ boundary R c L n g) := by
  letI : Module.FinitePresentation (Polynomial R) (finiteSections R c L) :=
    ContactRelativeChartFinitePresentation318.finite_chart R c L
  letI : Module.Finite (Polynomial R) (finiteKernel R c L n g) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker (finiteEvaluation R c L n g) hf)
  exact RelativePolynomialChartFinite318.finite_quotient R (overlapKernel R c L n g)
    (finiteKernel R c L n g) (infinityKernel R c L n g)
    (finiteMap R c L n g) (infinityMap R c L n g)
    (finite_polynomial R c L n g) (infinity_polynomial R c L n g)
    (finite_span R c L n g hf) (infinity_span R c L n g hi)

/-- Every sufficiently positive ORIGINAL geometric twist supplies one
finite global family whose chart evaluations are surjective and whose
actual coefficient relation quotient is finite. No global fp assertion
is made until this quotient is joined to the genuine H1 presentation. -/
theorem exists_presentation : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (r s : ℕ) (g : Fin r ⊕ Fin s → Γ((twist R c L (n : ℤ)).object,⊤)),
      Function.Surjective (finiteEvaluation R c L n g) ∧
      Function.Surjective (infinityEvaluation R c L n g) ∧
      Module.Finite R ((overlapKernel R c L n g) ⧸ boundary R c L n g) := by
  obtain ⟨N,hN⟩ := ContactRelativeGeneratorPresentations318.exists_presentations R c L
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨r,s,g,hf,hi,_,_⟩ := hN n hn
  exact ⟨r,s,g,hf,hi,finite R c L n g hf hi⟩
end ContactRelativeFiniteRelationQuotient318
