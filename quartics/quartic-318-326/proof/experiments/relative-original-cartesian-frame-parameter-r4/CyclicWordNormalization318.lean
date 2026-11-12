module
public import CyclicFrameTransport318
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public section
noncomputable section
open scoped Matrix
namespace CyclicWordNormalization318
open CyclicQuotientEvaluation318 FreeQuotientFramedClassifier318 CyclicFrameTransport318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (d : Framed R A ι) (w : ι → A)
@[expose] def columns : Matrix ι ι R := fun i j => evaluation d.action d.marked (w j) i
@[expose] def Normalized : Prop := ∀ j, evaluation d.action d.marked (w j)=Pi.single j 1

variable (h : IsUnit (columns R A ι d w).det)
/-- The SAME evaluation-column matrix is the invertible map from the
standard word frame to the original frame. -/
@[expose] def columnEquiv : (ι → R) ≃ₗ[R] (ι → R) :=
  Matrix.toLin'OfInv (M := (columns R A ι d w)⁻¹) (M' := columns R A ι d w)
    (Matrix.nonsing_inv_mul _ h) (Matrix.mul_nonsing_inv _ h)
lemma columnEquiv_basis (j : ι) :
    columnEquiv R A ι d w h (Pi.single j 1)=evaluation d.action d.marked (w j) := by
  change (columns R A ι d w) *ᵥ Pi.single j 1=_
  ext i
  simp only [Matrix.mulVec_single_one,Matrix.col_apply,columns]

/-- Normalize using the inverse of the actual word-column equivalence. -/
@[expose] def normalize : Framed R A ι :=
  changeFrame R A ι d (columnEquiv R A ι d w h).symm
lemma normalize_is_normalized : Normalized R A ι (normalize R A ι d w h) w := by
  intro j
  change evaluation (changeFrame R A ι d (columnEquiv R A ι d w h).symm).action
    (changeFrame R A ι d (columnEquiv R A ι d w h).symm).marked (w j)=_
  rw [evaluation_change,← columnEquiv_basis R A ι d w h j,LinearEquiv.symm_apply_apply]
lemma normalize_ideal : toIdeal R A ι (normalize R A ι d w h)=toIdeal R A ι d :=
  ideal_change R A ι d (columnEquiv R A ι d w h).symm
end CyclicWordNormalization318
