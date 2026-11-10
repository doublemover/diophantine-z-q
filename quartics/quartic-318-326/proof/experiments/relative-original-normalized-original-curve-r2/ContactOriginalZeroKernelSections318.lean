module
public import AffineQuotientKernelSections318
public import ContactGlobalZeroClosed318
public section
noncomputable section
namespace ContactOriginalZeroKernelSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))
local notation "p" => ContactGlobalSectionZero318.into R c L s
local notation "A" => CommRingCat.of (R ⊗[ℚ] finiteRing c)
local notation "B" => CommRingCat.of (R ⊗[ℚ] infinityRing c)

/-- Literal finite-chart kernel of the original globally glued zero map,
transported by its actual original chart coefficient isomorphism. -/
lemma finite_kernel :
    (RingHom.ker (p.app (AffineQuotientKernelSections318.chartOpen A
      (finiteInto R c)).1).hom).comap
      (AffineQuotientKernelSections318.coefficient A (finiteInto R c)).hom =
    finiteIdeal R c L s :=
  AffineQuotientKernelSections318.actual_kernel A (finiteIdeal R c L s) p
    (finiteInto R c) (ContactGlobalSectionZero318.finiteChart R c L s)
    (ContactGlobalZeroChartSquares318.finite_square R c L s)

/-- The same comparison on the WHOLE original infinity chart. Both use
the original glued section, and preserve nilpotent multiplicities. -/
lemma infinity_kernel :
    (RingHom.ker (p.app (AffineQuotientKernelSections318.chartOpen B
      (infinityInto R c)).1).hom).comap
      (AffineQuotientKernelSections318.coefficient B (infinityInto R c)).hom =
    infinityIdeal R c L s :=
  AffineQuotientKernelSections318.actual_kernel B (infinityIdeal R c L s) p
    (infinityInto R c) (ContactGlobalSectionZero318.infinityChart R c L s)
    (ContactGlobalZeroChartSquares318.infinity_square R c L s)
end ContactOriginalZeroKernelSections318
