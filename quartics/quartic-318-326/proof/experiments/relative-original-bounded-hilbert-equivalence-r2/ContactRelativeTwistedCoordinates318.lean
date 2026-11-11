module
public import ContactRelativeGeometricTwist318
public import OriginalTwoFrameTensorScalar318
public section
noncomputable section
namespace ContactRelativeTwistedCoordinates318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeWholeOpenSections318 ContactRelativeGeometricTwist318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (d : ℤ)
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

@[expose] def finiteCoordinates (V : (curve R c).Opens) (h : V ≤ finiteOpen R c) :=
  OriginalTensorUntwistOver318.sections L (line R c d) (finiteOpen R c) (finiteFrame R c d) V h
@[expose] def infinityCoordinates (V : (curve R c).Opens) (h : V ≤ infinityOpen R c) :=
  OriginalTensorUntwistOver318.sections L (line R c d) (infinityOpen R c) (infinityFrame R c d) V h

/-- Coordinates live in the SAME original Laurent section module. No
finite free basis is chosen over the arbitrary coefficient ring. -/
@[expose] def coordinates : Γ((twist R c L d).object,finiteOpen R c ⊓ infinityOpen R c) ≃+
    originalSections R c L :=
  (finiteCoordinates R c L d _ inf_le_left).toAddEquiv.trans (overlapEquiv R c L).symm

lemma scalar_square (s : Γ((twist R c L d).object,finiteOpen R c ⊓ infinityOpen R c)) :
    coordinates R c L d s = (LaurentPolynomial.T d : LaurentPolynomial R) •
      (overlapEquiv R c L).symm (infinityCoordinates R c L d _ inf_le_right s) := by
  have h := OriginalTwoFrameTensorScalar318.scalar_square L (line R c d)
    (finiteOpen R c) (infinityOpen R c) (finiteFrame R c d) (infinityFrame R c d)
    (transition R c d) (frame_relation R c d) s
  change (overlapEquiv R c L).symm (finiteCoordinates R c L d _ inf_le_left s) = _
  rw [show finiteCoordinates R c L d _ inf_le_left s =
    scalar R c (LaurentPolynomial.T d) • infinityCoordinates R c L d _ inf_le_right s from h]
  exact inverse_scalar R c L _ _

lemma finite_restriction (s : Γ((twist R c L d).object,finiteOpen R c)) :
    coordinates R c L d ((twist R c L d).object.presheaf.map (homOfLE inf_le_left).op s) =
      finiteRestriction R c L ((finiteEquiv R c L).symm
        (finiteCoordinates R c L d (finiteOpen R c) le_rfl s)) := by
  apply (overlapEquiv R c L).injective
  change overlapEquiv R c L ((overlapEquiv R c L).symm
    (finiteCoordinates R c L d _ inf_le_left
      ((twist R c L d).object.presheaf.map (homOfLE inf_le_left).op s))) = _
  rw [AddEquiv.apply_symm_apply,ContactRelativeWholeOpenSections318.finite_square,AddEquiv.apply_symm_apply]
  exact (OriginalTensorUntwistOver318.natural L (line R c d) (finiteOpen R c)
    (finiteFrame R c d) le_rfl inf_le_left s).symm

lemma infinity_restriction (s : Γ((twist R c L d).object,infinityOpen R c)) :
    coordinates R c L d ((twist R c L d).object.presheaf.map (homOfLE inf_le_right).op s) =
      (LaurentPolynomial.T d : LaurentPolynomial R) • infinityRestriction R c L
        ((infinityEquiv R c L).symm (infinityCoordinates R c L d (infinityOpen R c) le_rfl s)) := by
  rw [scalar_square]
  congr 1
  apply (overlapEquiv R c L).injective
  rw [AddEquiv.apply_symm_apply,ContactRelativeWholeOpenSections318.infinity_square,AddEquiv.apply_symm_apply]
  exact (OriginalTensorUntwistOver318.natural L (line R c d) (infinityOpen R c)
    (infinityFrame R c d) le_rfl inf_le_right s).symm
end ContactRelativeTwistedCoordinates318
