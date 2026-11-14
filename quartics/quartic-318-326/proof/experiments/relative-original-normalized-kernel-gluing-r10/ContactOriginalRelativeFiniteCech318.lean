module
public import ContactOriginalRelativeOverlapSpan318
public import RelativePolynomialChartFinite318
public section
noncomputable section
namespace ContactOriginalRelativeFiniteCech318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
open ContactOriginalRelativeLineOverlap318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L)
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)
local instance : Module R (finiteSections R c L) :=
  Module.compHom (finiteSections R c L) Polynomial.C
local instance : Module R (infinitySections R c L) :=
  Module.compHom (infinitySections R c L) Polynomial.C

/-- The exact original coefficient Cech quotient is finite on EVERY
actual affine test, including nonreduced and non-Noetherian tests. Both
restriction images and the overlap module are the SAME original objects.
The finite exponent window and all its hypotheses are constructed from
the actual line, not supplied as inputs. Identification with the ambient
whole-open derived H1, base-change and represented Picard remain separate. -/
theorem finite_quotient : Module.Finite R
    (originalSections R c L ⧸
      ((ContactOriginalRelativeOverlapSpan318.finiteMap R c L).range ⊔
        (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).range)) := by
  apply RelativePolynomialChartFinite318.finite_quotient R (originalSections R c L)
    (finiteSections R c L) (infinitySections R c L)
    (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
    (ContactOriginalRelativeOverlapSpan318.infinityMap R c L)
  · exact finite_polynomial R c L
  · exact infinity_polynomial R c L
  · exact ContactOriginalRelativeOverlapSpan318.finite_span R c L
  · exact ContactOriginalRelativeOverlapSpan318.infinity_span R c L
end ContactOriginalRelativeFiniteCech318
