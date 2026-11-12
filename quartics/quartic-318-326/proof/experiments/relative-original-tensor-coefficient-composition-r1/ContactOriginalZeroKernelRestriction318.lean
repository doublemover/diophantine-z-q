module
public import AffineZeroKernelRestriction318
public import ContactOriginalZeroKernelSections318
public section
noncomputable section
namespace ContactOriginalZeroKernelRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionZeros318
open AffineQuotientKernelSections318 AffineZeroKernelRestriction318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))
local notation "p" => ContactGlobalSectionZero318.into R c L s
local notation "A" => CommRingCat.of (R ⊗[ℚ] finiteRing c)
local notation "B" => CommRingCat.of (R ⊗[ℚ] infinityRing c)

/-- The actual finite-chart section ideal produces the SAME global
zero-map kernel on every affine subopen, not only at chart-top. -/
lemma finite_kernel (V : (curve R c).affineOpens)
    (h : V≤chartOpen A (finiteInto R c)) :
    RingHom.ker (p.app V.1).hom =
      Ideal.map (restrictedCoefficient A (finiteInto R c) V h).hom (finiteIdeal R c L s) :=
  restricted_kernel A (finiteIdeal R c L s) p (finiteInto R c)
    (ContactGlobalSectionZero318.finiteChart R c L s)
    (ContactGlobalZeroChartSquares318.finite_square R c L s) V h

/-- The corresponding WHOLE infinity-chart producer on all its affine
subopens uses the same original global section and original zero map. -/
lemma infinity_kernel (V : (curve R c).affineOpens)
    (h : V≤chartOpen B (infinityInto R c)) :
    RingHom.ker (p.app V.1).hom =
      Ideal.map (restrictedCoefficient B (infinityInto R c) V h).hom (infinityIdeal R c L s) :=
  restricted_kernel B (infinityIdeal R c L s) p (infinityInto R c)
    (ContactGlobalSectionZero318.infinityChart R c L s)
    (ContactGlobalZeroChartSquares318.infinity_square R c L s) V h
end ContactOriginalZeroKernelRestriction318
