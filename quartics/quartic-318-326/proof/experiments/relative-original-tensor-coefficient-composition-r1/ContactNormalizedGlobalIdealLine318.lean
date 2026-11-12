module
public import ActualCartierIdealLine318
public import ContactNormalizedGlobalCartier318
public import FramedLineInverse318
public section
noncomputable section
namespace ContactNormalizedGlobalIdealLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactNormalizedGlobalClosedFamily318.into R c L hz
local notation "X" => ContactNormalizedGlobalClosedFamily318.ambient R c L hz

/-- The ideal of the SAME global normalized closed finite-flat Cartier
family, now as an ACTUAL invertible module sheaf on the original ambient
curve. Its frames and every regularity input are constructed internally. -/
@[expose] def idealLine : Line X :=
  ActualCartierIdealLine318.line p (ContactNormalizedGlobalCartier318.regular_charts R c L hz)
lemma idealLine_object : (idealLine R c L hz).object=ActualClosedIdealModule318.object p := rfl

@[expose] def inclusion : (idealLine R c L hz).object ⟶ SheafOfModules.unit X.ringCatSheaf :=
  ActualClosedIdealModule318.inclusion p
instance inclusion_mono : Mono (inclusion R c L hz) :=
  inferInstanceAs (Mono (ActualClosedIdealModule318.inclusion p))

/-- The genuine divisor line O(D), defined as the dual of the ACTUAL
invertible ideal O(-D), not as a new freely chosen parameter line. -/
@[expose] def divisorLine : Line X := FramedLineInverse318.inverse (idealLine R c L hz)

lemma ideal_sections (V : X.affineOpens) :
    LinearMap.ker
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op V.1)).map
        (ActualClosedIdealModule318.structure p)).hom=p.ker.ideal V :=
  ActualClosedIdealModule318.section_kernel_idealData p V
end ContactNormalizedGlobalIdealLine318
