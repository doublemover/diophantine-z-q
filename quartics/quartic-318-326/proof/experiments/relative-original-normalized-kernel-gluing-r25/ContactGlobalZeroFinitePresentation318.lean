module
public import ContactGlobalZeroClosed318
public import OriginalAffineZeroFinitePresentation318
public section
noncomputable section
namespace ContactGlobalZeroFinitePresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalSectionZeros318 ContactGlobalZeroChartSquares318 ContactGlobalZeroClosed318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L : Line (curve R c)) (s : Γ(L.object,⊤))

/-- The original global zero closed immersion is locally finitely
presented over every coefficient ring, without a Noetherian shortcut.
The finite equations are constructed from actual finite projective dual
frames and consumed on the SAME whole-chart pullback squares. -/
instance finitePresentation : LocallyOfFinitePresentation (ContactGlobalSectionZero318.into R c L s) := by
  apply IsZariskiLocalAtTarget.of_openCover (originalCover R c)
  intro i
  fin_cases i
  · have h := (finite_square R c L s).flip
    haveI : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s)))) :=
      OriginalAffineZeroFinitePresentation318.finitePresentation _ (finiteLine R c L) (finiteSection R c L s)
    have hc : LocallyOfFinitePresentation (h.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal R c L s)))) := inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
  · have h := (infinity_square R c L s).flip
    haveI : LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s)))) :=
      OriginalAffineZeroFinitePresentation318.finitePresentation _ (infinityLine R c L) (infinitySection R c L s)
    have hc : LocallyOfFinitePresentation (h.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal R c L s)))) := inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
end ContactGlobalZeroFinitePresentation318
