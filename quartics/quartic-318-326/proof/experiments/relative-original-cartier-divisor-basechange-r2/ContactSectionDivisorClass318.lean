module
public import ContactProjectiveDivisorLine318
public import ContactSectionQuotientCartier318
public import ContactResidueActualIdealLine318
public section
noncomputable section
namespace ContactSectionDivisorClass318
open AlgebraicGeometry CategoryTheory LineSheafClass318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (ContactOriginalRelativePolynomialCharts318.curve R c)) (s : Γ(L.object,⊤))
  (hs : ContactResidueRegularFlat318.ResidueNonzero R c L s)
local notation "D" => ContactSectionQuotientData318.datum R c L s
local notation "p" => ContactProjectiveQuotientGluing318.into R c D
local notation "q" => ContactGlobalSectionZero318.into R c L s
local notation "hp" => ContactSectionQuotientCartier318.regular_charts R c L s hs
local notation "hq" => ContactResidueCartierCharts318.regular_charts R c L s hs
/-- The actual new projective kernel line is the original section line's
inverse, via whole ideal equality and the historical actual kernel iso. -/
@[expose] def inverseKernelIso : (FramedLineInverse318.inverse L).object ≅
    (ActualCartierIdealLine318.line p hp).object :=
  ContactResidueActualIdealLine318.iso R c L s hs ≪≫
    (CartierKernelEquality318.iso p q hp hq
      (ContactSectionQuotientProperties318.idealSheaf_eq R c L s)).symm
@[expose] def divisorLine : Line (ContactOriginalRelativePolynomialCharts318.curve R c) :=
  ContactProjectiveDivisorLine318.line R c D
    (ContactSectionQuotientCartier318.finite_regular R c L s hs)
    (ContactSectionQuotientCartier318.infinity_regular R c L s hs)
/-- The sign is computed: dualizing the actual inverse kernel recovers
the ORIGINAL line class, on the whole possibly nonreduced base. -/
lemma divisor_class : classOf (divisorLine R c L s hs)=classOf L := by
  have h : classOf (FramedLineInverse318.inverse L)=classOf (ActualCartierIdealLine318.line p hp) :=
    LineSheafClass318.classOf_eq (inverseKernelIso R c L s hs)
  change classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line p hp))=classOf L
  rw [LineSheafClassGroup318.classOf_inverse,← h,LineSheafClassGroup318.classOf_inverse,inv_inv]
end ContactSectionDivisorClass318
