module
public import ContactProjectiveQuotientProperties318
public import ContactOriginalSectionZeros318
public import ContactGlobalZeroClosed318
public import ContactGlobalResidueFlat318
public section
noncomputable section
namespace ContactSectionQuotientData318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (ContactOriginalRelativePolynomialCharts318.curve R c)) (s : Γ(L.object,⊤))
/-- The existing original global section produces the compatible arbitrary
quotient datum through its proved WHOLE overlap ideal equations. -/
@[expose] def datum : ContactProjectiveQuotientData318.Datum R c where
  finiteIdeal := ContactOriginalSectionZeros318.finiteIdeal R c L s
  infinityIdeal := ContactOriginalSectionZeros318.infinityIdeal R c L s
  compatible := ContactOriginalSectionZeros318.same_overlap R c L s
end ContactSectionQuotientData318
