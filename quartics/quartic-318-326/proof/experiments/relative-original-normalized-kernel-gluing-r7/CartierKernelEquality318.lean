module
public import CartierIdealClass318
public section
noncomputable section
namespace CartierKernelEquality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {Z W X : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ X)
  [QuasiCompact p] [QuasiCompact q]
  (hp : OriginalRegularClosedCharts318.Property p) (hq : OriginalRegularClosedCharts318.Property q)
  (h : p.ker=q.ker)
/-- Equality of FULL closed ideal sheaves induces an actual isomorphism
of their invertible kernel modules, preserving the original inclusions. -/
@[expose] def iso : (ActualCartierIdealLine318.line p hp).object ≅
    (ActualCartierIdealLine318.line q hq).object :=
  InvertibleIdealUniqueness318.iso q (ActualCartierIdealLine318.line p hp)
    (ActualClosedIdealModule318.inclusion p) (fun V => by
      rw [ActualClosedIdealRange318.range_ideal,h])
@[reassoc] lemma iso_inclusion : (iso p q hp hq h).hom ≫ ActualClosedIdealModule318.inclusion q=
    ActualClosedIdealModule318.inclusion p :=
  InvertibleIdealUniqueness318.inclusion q (ActualCartierIdealLine318.line p hp)
    (ActualClosedIdealModule318.inclusion p) (fun V => by
      rw [ActualClosedIdealRange318.range_ideal,h])
include h in
lemma class_eq : CartierIdealClass318.value p hp=CartierIdealClass318.value q hq :=
  LineSheafClass318.classOf_eq (iso p q hp hq h)
end CartierKernelEquality318
