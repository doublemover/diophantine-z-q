module
public import ContactRelativeBoundedClass318
public section
noncomputable section
namespace ContactNormalizedPairData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (A B : Line (curve R c))
  (hA : ∀ x : NonreducedLineMayerVietoris318.H1 A,x=0)
  (hB : ∀ x : NonreducedLineMayerVietoris318.H1 B,x=0)
abbrev firstBase := ContactNormalizedSectionParameter318.projection R c A hA
abbrev secondBase := ContactNormalizedSectionParameter318.projection R c B hB
abbrev space := RelativePairParameter318.space (firstBase R c A hA) (secondBase R c B hB)
abbrev projection : space R c A B hA hB ⟶ Spec R :=
  RelativePairParameter318.projection (firstBase R c A hA) (secondBase R c B hB)
abbrev first := RelativePairParameter318.first (firstBase R c A hA) (secondBase R c B hB)
abbrev second := RelativePairParameter318.second (firstBase R c A hA) (secondBase R c B hB)
lemma first_over : first R c A B hA hB ≫ firstBase R c A hA=projection R c A B hA hB := rfl
lemma second_over : second R c A B hA hB ≫ secondBase R c B hB=projection R c A B hA hB :=
  RelativePairParameter318.second_over _ _
abbrev firstBound := ContactNormalizedParameterCompact318.bound R c A hA
abbrev secondBound := ContactNormalizedParameterCompact318.bound R c B hB
/-- Both actual whole Cartier families now live on ONE genuine common
parameter, with their original independently produced numerical bounds. -/
@[expose] def firstData : ContactBoundedCartierEquiv318.Data c (firstBound R c A hA)
    (projection R c A B hA hB ≫ baseMap R) :=
  ContactBoundedCartierBaseChange318.map c (firstBound R c A hA)
    (firstBase R c A hA ≫ baseMap R) (projection R c A B hA hB ≫ baseMap R)
    (first R c A B hA hB) (by rw [←Category.assoc,first_over])
    (ContactNormalizedBoundedCartier318.data R c A hA)
@[expose] def secondData : ContactBoundedCartierEquiv318.Data c (secondBound R c B hB)
    (projection R c A B hA hB ≫ baseMap R) :=
  ContactBoundedCartierBaseChange318.map c (secondBound R c B hB)
    (secondBase R c B hB ≫ baseMap R) (projection R c A B hA hB ≫ baseMap R)
    (second R c A B hA hB) (by rw [←Category.assoc,second_over])
    (ContactNormalizedBoundedCartier318.data R c B hB)
@[expose] def firstPoint := ContactBoundedCartierEquiv318.equivalence c (firstBound R c A hA)
  (projection R c A B hA hB ≫ baseMap R) (firstData R c A B hA hB)
@[expose] def secondPoint := ContactBoundedCartierEquiv318.equivalence c (secondBound R c B hB)
  (projection R c A B hA hB ≫ baseMap R) (secondData R c A B hA hB)
end ContactNormalizedPairData318
