module
public import VaryingNormalizedWordOverlap318
public import VaryingNormalizedFrameEquiv318
public import CyclicWordFrameCocycle318
public section
noncomputable section
namespace VaryingNormalizedOverlapFrames318
open VaryingNormalizedWordOverlap318 VaryingNormalizedFrameEquiv318
open VaryingSourceTensorAction318 VaryingNormalizedWordFrame318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S] (v : ι → List A)
local notation "B" => (S ⊗[R] A)
local notation "words" t => (fun j => (1 : S) ⊗ₜ[R] (t j).prod)

lemma frame_columns (d : VaryingNormalizedWordParameter318.Point R A ι w S) :
    CyclicWordNormalization318.columns S B ι (toFrame R A ι w S d).val (words v)=
      VaryingMatrixWords318.columns d.val.val v := by
  ext i j
  change CyclicQuotientEvaluation318.evaluation
    (linearAction R A ι S (sourceAction R A ι w S d))
      (sourceAction R A ι w S d).marked ((1 : S) ⊗ₜ[R] (v j).prod) i=_
  rw [word_evaluation,source_point]
  rfl

abbrev OverlapFrames := CyclicWordFrameOverlap318.Overlap S B ι (words w) (words v)
@[expose] def toFrames (d : Point R A ι w S v) : OverlapFrames R A ι w S v :=
  ⟨toFrame R A ι w S d.val,by
    rw [frame_columns]
    exact d.property⟩
@[expose] def fromFrames (d : OverlapFrames R A ι w S v) : Point R A ι w S v :=
  ⟨fromFrame R A ι w S d.val,by
    rw [← frame_columns]
    change IsUnit (CyclicWordNormalization318.columns S B ι
      ((frames R A ι w S) ((frames R A ι w S).symm d.val)).val (words v)).det
    rw [Equiv.apply_symm_apply]
    exact d.property⟩

@[expose] def overlapFrames : Point R A ι w S v ≃ OverlapFrames R A ι w S v where
  toFun := toFrames R A ι w S v
  invFun := fromFrames R A ι w S v
  left_inv d := by
    apply Subtype.ext
    exact (frames R A ι w S).symm_apply_apply d.val
  right_inv d := by
    apply Subtype.ext
    exact (frames R A ι w S).apply_symm_apply d.val

/-- This equivalence changes the actual full source action and marked
vector by the inverse word matrix, not a field-only orbit relation. -/
@[expose] def transition : Point R A ι w S v ≃ Point R A ι v S w :=
  (overlapFrames R A ι w S v).trans
    ((CyclicWordFrameOverlap318.overlapEquiv S B ι (words w) (words v)).trans
      (overlapFrames R A ι v S w).symm)
end VaryingNormalizedOverlapFrames318
