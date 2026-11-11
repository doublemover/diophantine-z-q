module
public import OriginalTensorUntwistRefinement318
public import ContactOriginalTensorOverlapCoordinates318
public section
noncomputable section
namespace ContactOriginalTwistedRestriction318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
open ContactOriginalCohomologyCoordinates318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c)) (d : ℤ)
abbrev W := finiteOpen c ⊓ infinityOpen c

def finiteSections (V : (ContactProjectiveModel318.model c).Opens) (h : V ≤ finiteOpen c) :=
  OriginalTensorUntwistOver318.sections L (line c d) (finiteOpen c) (finiteFrame c d) V h

def infinitySections (V : (ContactProjectiveModel318.model c).Opens) (h : V ≤ infinityOpen c) :=
  OriginalTensorUntwistOver318.sections L (line c d) (infinityOpen c) (infinityFrame c d) V h

/-- Coordinates on the original twisted overlap, anchored in the original
finite-chart untwisting and the SAME old Laurent coordinates of L. -/
def coordinates : Γ((twist c L d).object,W c) ≃+
    LaurentVectorFiltration318.V ℚ (ContactOriginalLaurentCoordinates318.finiteRank c L) :=
  (finiteSections c L d (W c) inf_le_left).toAddEquiv.trans (overlapCoordinates c L)

/-- The genuine infinity/finite scalar square on ALL original overlap
sections, after exact chart refinement and image-of-top comparisons. -/
lemma scalar_square (s : Γ((twist c L d).object,W c)) :
    coordinates c L d s = (LaurentPolynomial.T d : OriginalLaurentProjectiveOverlap318.Ring) •
      overlapCoordinates c L (infinitySections c L d (W c) inf_le_right s) := by
  let t := (OriginalRestrictionTopScalar318.moduleTop (twist c L d).object (W c)).symm s
  have h := ContactOriginalTensorOverlapCoordinates318.monomial_square c L d t
  have hf := OriginalTensorUntwistOver318.top_square L (line c d) (W c)
    (OpenLineFrameRefinement318.frame (line c d).object (finiteOpen c)
      (finiteFrame c d).symm (W c) inf_le_left).symm t
  have hi := OriginalTensorUntwistOver318.top_square L (line c d) (W c)
    (OpenLineFrameRefinement318.frame (line c d).object (infinityOpen c)
      (infinityFrame c d).symm (W c) inf_le_right).symm t
  have ht : OriginalRestrictionTopScalar318.moduleTop (twist c L d).object (W c) t = s :=
    AddEquiv.apply_symm_apply _ s
  rw [ht] at hf hi
  rw [← OriginalTensorUntwistRefinement318.sections L (line c d) (finiteOpen c)
    (finiteFrame c d) (W c) inf_le_left (W c) le_rfl s] at hf
  rw [← OriginalTensorUntwistRefinement318.sections L (line c d) (infinityOpen c)
    (infinityFrame c d) (W c) inf_le_right (W c) le_rfl s] at hi
  change overlapCoordinates c L
      (OriginalRestrictionTopScalar318.moduleTop L.object (W c)
        ((ContactOriginalTensorOverlapCoordinates318.leftIso c L d).hom.app ⊤ t)) =
    (LaurentPolynomial.T d : OriginalLaurentProjectiveOverlap318.Ring) •
      overlapCoordinates c L (OriginalRestrictionTopScalar318.moduleTop L.object (W c)
        ((ContactOriginalTensorOverlapCoordinates318.rightIso c L d).hom.app ⊤ t)) at h
  exact (congrArg (overlapCoordinates c L) hf).trans
    (h.trans (congrArg (fun z => (LaurentPolynomial.T d : OriginalLaurentProjectiveOverlap318.Ring) •
      overlapCoordinates c L z) hi.symm))

/-- Literal finite-chart restriction, not a chosen matrix map. -/
lemma finite_restriction (s : Γ((twist c L d).object,finiteOpen c)) :
    coordinates c L d ((twist c L d).object.presheaf.map (homOfLE inf_le_left).op s) =
      overlapCoordinates c L (L.object.presheaf.map (homOfLE inf_le_left).op
        (finiteSections c L d (finiteOpen c) le_rfl s)) := by
  exact congrArg (overlapCoordinates c L)
    (OriginalTensorUntwistOver318.natural L (line c d) (finiteOpen c) (finiteFrame c d)
      le_rfl inf_le_left s).symm

/-- Literal infinity-chart restriction is T^d times the original L
restriction. Both old section spaces and their original maps are retained. -/
lemma infinity_restriction (s : Γ((twist c L d).object,infinityOpen c)) :
    coordinates c L d ((twist c L d).object.presheaf.map (homOfLE inf_le_right).op s) =
      (LaurentPolynomial.T d : OriginalLaurentProjectiveOverlap318.Ring) •
        overlapCoordinates c L (L.object.presheaf.map (homOfLE inf_le_right).op
          (infinitySections c L d (infinityOpen c) le_rfl s)) := by
  rw [scalar_square]
  exact congrArg (fun z => (LaurentPolynomial.T d : OriginalLaurentProjectiveOverlap318.Ring) •
    overlapCoordinates c L z)
    (OriginalTensorUntwistOver318.natural L (line c d) (infinityOpen c) (infinityFrame c d)
      le_rfl inf_le_right s).symm
end ContactOriginalTwistedRestriction318
