module
public import CyclicNormalizedIdealClassifier318
public section
noncomputable section
open scoped Matrix
namespace CyclicWordFrameOverlap318
open CyclicQuotientEvaluation318 FreeQuotientFramedClassifier318
open CyclicWordNormalization318 CyclicNormalizedIdealClassifier318
open CyclicNormalizedFrameUniqueness318 CyclicFrameTransport318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
section MatrixLemmas
variable (d : Framed R A ι) (v : ι → A) (hv : IsUnit (columns R A ι d v).det)

lemma normalize_columns (u : ι → A) :
    columns R A ι (normalize R A ι d v hv) u=
      (columns R A ι d v)⁻¹ * columns R A ι d u := by
  ext i j
  change evaluation (normalize R A ι d v hv).action
    (normalize R A ι d v hv).marked (u j) i=_
  rw [show evaluation (normalize R A ι d v hv).action
    (normalize R A ι d v hv).marked (u j)=
      (columnEquiv R A ι d v hv).symm (evaluation d.action d.marked (u j)) from
    evaluation_change R A ι d (columnEquiv R A ι d v hv).symm (u j)]
  change ((columns R A ι d v)⁻¹ *ᵥ evaluation d.action d.marked (u j)) i=_
  simp only [Matrix.mulVec_apply_eq_sum,Matrix.mul_apply,columns]

lemma unit_after_normalize (u : ι → A) (hu : IsUnit (columns R A ι d u).det) :
    IsUnit (columns R A ι (normalize R A ι d v hv) u).det := by
  rw [normalize_columns,Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr hv).mul hu

lemma normalized_columns (w : ι → A) (h : Normalized R A ι d w) :
    columns R A ι d w=1 := by
  ext i j
  change evaluation d.action d.marked (w j) i=(1 : Matrix ι ι R) i j
  rw [h j]
  simp only [Pi.single_apply,Matrix.one_apply,eq_comm]
lemma normalized_unit (w : ι → A) (h : Normalized R A ι d w) :
    IsUnit (columns R A ι d w).det := by
  rw [normalized_columns R A ι d w h,Matrix.det_one]
  exact isUnit_one

end MatrixLemmas

variable (w v : ι → A)
abbrev Overlap := {d : NormalizedFrames R A ι w // IsUnit (columns R A ι d.val v).det}
@[expose] def transition (d : Overlap R A ι w v) : Overlap R A ι v w :=
  ⟨⟨normalize R A ι d.val.val v d.property,
    normalize_is_normalized R A ι d.val.val v d.property⟩,
    unit_after_normalize R A ι d.val.val v d.property w
      (normalized_unit R A ι d.val.val w d.val.property)⟩

lemma transition_inverse (d : Overlap R A ι w v) :
    transition R A ι v w (transition R A ι w v d)=d := by
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_ideal R A ι _ _ w
    (transition R A ι v w (transition R A ι w v d)).val.property d.val.property
  exact (normalize_ideal R A ι _ w _).trans (normalize_ideal R A ι d.val.val v d.property)

/-- Actual word-frame overlaps are two-sided equivalences over the whole
ring, preserving the full original ideal at every step. -/
@[expose] def overlapEquiv : Overlap R A ι w v ≃ Overlap R A ι v w where
  toFun := transition R A ι w v
  invFun := transition R A ι v w
  left_inv := transition_inverse R A ι w v
  right_inv := transition_inverse R A ι v w
end CyclicWordFrameOverlap318
