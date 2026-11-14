module
public import ContactNormalizedGlobalIdealLine318
public import LineArrowInverseRegular318
public import ActualClosedIdealRange318
public section
noncomputable section
namespace ContactNormalizedDivisorSection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local notation "p" => ContactNormalizedGlobalClosedFamily318.into R c L hz
local notation "X" => ContactNormalizedGlobalClosedFamily318.ambient R c L hz
local notation "I" => ContactNormalizedGlobalIdealLine318.idealLine R c L hz
local notation "D" => ContactNormalizedGlobalIdealLine318.divisorLine R c L hz
local notation "f" => ContactNormalizedGlobalIdealLine318.inclusion R c L hz

/-- Canonical global section of the genuine inverse ideal line, formed
from the original inclusion itself, not an assumed identification with a
linear dual or a section on an unrelated parameter model. -/
@[expose] def section : Γ(D.object,⊤) := LineArrowInverseSection318.section I f

lemma coordinate (i : I.Index) (V : X.Opens) (hV : V≤I.opens i) :
    (LineArrowInverseLocal318.inverseFrame I i V hV).symm
      (D.object.presheaf.map (homOfLE (show V≤⊤ from le_top)).op (section R c L hz))=
      LineArrowInverseLocal318.coefficient I f i V hV :=
  LineArrowInverseSection318.section_coordinate I f i V hV

lemma regular (i : I.Index) (V : X.Opens) (hV : V≤I.opens i) :
    ∀ a : Γ(X,V),a*LineArrowInverseLocal318.coefficient I f i V hV=0 → a=0 :=
  LineArrowInverseRegular318.regular I f i V hV

/-- The zero ideal of this canonical divisor section is EXACTLY the
original globally glued closed-family ideal on every framed affine open.
This keeps all nilpotents and scheme structure, not just the same support. -/
lemma original_zero_ideal (i : I.Index) (V : X.affineOpens) (hV : V≤I.opens i) :
    Ideal.span {LineArrowInverseLocal318.coefficient I f i V.1 hV}=p.ker.ideal V :=
  (LineArrowInverseRegular318.image I f i V.1 hV).symm.trans
    (ActualClosedIdealRange318.range_ideal p V)
end ContactNormalizedDivisorSection318
