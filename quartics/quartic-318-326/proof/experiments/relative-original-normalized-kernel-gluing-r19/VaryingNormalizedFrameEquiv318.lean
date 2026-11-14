module
public import VaryingNormalizedWordFrame318
public import CyclicNormalizedIdealClassifier318
public section
noncomputable section
namespace VaryingNormalizedFrameEquiv318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open VaryingSourceFreeQuotientClassifier318 VaryingNormalizedWordFrame318
open VaryingNormalizedWordParameter318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]
local notation "B" => (S ⊗[R] A)
local notation "words" => (fun j => (1 : S) ⊗ₜ[R] (w j).prod)
abbrev Frames := CyclicNormalizedIdealClassifier318.NormalizedFrames S B ι words
@[expose] def toFrame (d : Point R A ι w S) : Frames R A ι w S :=
  ⟨framed R A ι w S d,normalized R A ι w S d⟩
@[expose] def fromFrame (d : Frames R A ι w S) : Point R A ι w S :=
  ⟨point R A ι S (fromFramedData R A ι S d.val),by
    ext i j
    have hv : VaryingMatrixWords318.wordVector
        (point R A ι S (fromFramedData R A ι S d.val)).val (w j)=Pi.single j 1 := by
      calc
        _=CyclicQuotientEvaluation318.evaluation
            (linearAction R A ι S (fromFramedData R A ι S d.val))
            (fromFramedData R A ι S d.val).marked (words j) :=
          (word_evaluation R A ι S (fromFramedData R A ι S d.val) (w j)).symm
        _=CyclicQuotientEvaluation318.evaluation d.val.action d.val.marked (words j) := by
          rw [fromFramed_action]
        _=Pi.single j 1 := d.property j
    change VaryingMatrixWords318.wordVector
      (point R A ι S (fromFramedData R A ι S d.val)).val (w j) i=(1 : Matrix ι ι S) i j
    rw [hv]
    simp only [Pi.single_apply,Matrix.one_apply,eq_comm]⟩

private lemma frame_ext {a b : FreeQuotientFramedClassifier318.Framed S B ι}
    (hm : a.action=b.action) (hv : a.marked=b.marked) : a=b := by
  cases a
  cases b
  cases hm
  cases hv
  rfl

@[expose] def frames : Point R A ι w S ≃ Frames R A ι w S where
  toFun := toFrame R A ι w S
  invFun := fromFrame R A ι w S
  left_inv d := by
    apply Subtype.ext
    change point R A ι S (fromFramedData R A ι S
      (toFramed R A ι S (cyclic R A ι w S d)))=d.val
    rw [from_to_data]
    exact source_point R A ι w S d
  right_inv d := by
    apply Subtype.ext
    apply frame_ext R A ι S
    · change linearAction R A ι S
        (action R A ι S (point R A ι S (fromFramedData R A ι S d.val)))=d.val.action
      have h : action R A ι S (point R A ι S (fromFramedData R A ι S d.val))=
          fromFramedData R A ι S d.val :=
        (actionPoints R A ι S).apply_symm_apply (fromFramedData R A ι S d.val)
      rw [h,fromFramed_action]
    · rfl
end VaryingNormalizedFrameEquiv318
