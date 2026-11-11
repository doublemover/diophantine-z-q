module
public import ContactBoundedCartierNaturality318
public import LineArrowInverseRegular318
public section
noncomputable section
namespace CartierCanonicalSection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (hp : OriginalRegularClosedCharts318.Property p)
abbrev idealLine := ActualCartierIdealLine318.line p hp
abbrev divisorLine := FramedLineInverse318.inverse (idealLine p hp)
@[expose] def section : Γ((divisorLine p hp).object,⊤) :=
  LineArrowInverseSection318.section (idealLine p hp) (ActualClosedIdealModule318.inclusion p)
variable (i : (idealLine p hp).Index) (V : X.Opens) (hV : V≤(idealLine p hp).opens i)
lemma coordinate :
    (LineArrowInverseLocal318.inverseFrame (idealLine p hp) i V hV).symm
      ((divisorLine p hp).object.presheaf.map (homOfLE (show V≤⊤ from le_top)).op (section p hp))=
    LineArrowInverseLocal318.coefficient (idealLine p hp) (ActualClosedIdealModule318.inclusion p) i V hV :=
  LineArrowInverseSection318.section_coordinate (idealLine p hp) (ActualClosedIdealModule318.inclusion p) i V hV
lemma regular : ∀ a : Γ(X,V),a*LineArrowInverseLocal318.coefficient
    (idealLine p hp) (ActualClosedIdealModule318.inclusion p) i V hV=0 → a=0 :=
  LineArrowInverseRegular318.regular (idealLine p hp) (ActualClosedIdealModule318.inclusion p) i V hV
/-- On every actual framed affine open the canonical divisor section
has precisely the original FULL ideal, not only its radical. -/
lemma ideal (W : X.affineOpens) (hW : W≤(idealLine p hp).opens i) :
    Ideal.span {LineArrowInverseLocal318.coefficient (idealLine p hp)
      (ActualClosedIdealModule318.inclusion p) i W.1 hW}=p.ker.ideal W :=
  (LineArrowInverseRegular318.image (idealLine p hp) (ActualClosedIdealModule318.inclusion p) i W.1 hW).symm.trans
    (ActualClosedIdealRange318.range_ideal p W)
end CartierCanonicalSection318
