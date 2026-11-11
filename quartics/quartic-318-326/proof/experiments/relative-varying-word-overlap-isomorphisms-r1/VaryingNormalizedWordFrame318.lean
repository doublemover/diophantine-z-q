module
public import VaryingNormalizedWordParameter318
public import VaryingSourceFreeQuotientClassifier318
public import CyclicNormalizedFrameUniqueness318
public section
noncomputable section
namespace VaryingNormalizedWordFrame318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open VaryingSourceFreeQuotientClassifier318 VaryingNormalizedWordParameter318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (d : Point R A ι w S)
@[expose] def sourceAction : Action R A ι S := action R A ι S d.val
lemma source_point : point R A ι S (sourceAction R A ι w S d)=d.val :=
  (actionPoints R A ι S).symm_apply_apply d.val
lemma determinant_unit : IsUnit (VaryingMatrixWords318.determinant
    (point R A ι S (sourceAction R A ι w S d)).val w) := by
  rw [source_point]
  change IsUnit (VaryingMatrixWords318.columns d.val.val w).det
  rw [d.property,Matrix.det_one]
  exact isUnit_one
@[expose] def cyclic : Cyclic R A ι S :=
  ⟨sourceAction R A ι w S d,VaryingSourceWordQuotient318.cyclic R A ι S
    (sourceAction R A ι w S d) w (determinant_unit R A ι w S d)⟩
@[expose] def framed : FreeQuotientFramedClassifier318.Framed S (S ⊗[R] A) ι :=
  toFramed R A ι S (cyclic R A ι w S d)

/-- The represented normalized equations fix the actual tensor-source
word evaluations, not a proxy multiplication table. -/
lemma normalized : CyclicWordNormalization318.Normalized S (S ⊗[R] A) ι
    (framed R A ι w S d) (fun j => (1 : S) ⊗ₜ[R] (w j).prod) := by
  intro j
  change CyclicQuotientEvaluation318.evaluation
    (linearAction R A ι S (sourceAction R A ι w S d))
      (sourceAction R A ι w S d).marked ((1 : S) ⊗ₜ[R] (w j).prod)=Pi.single j 1
  rw [word_evaluation,source_point]
  ext i
  have h := congrFun (congrFun d.property i) j
  simpa only [VaryingMatrixWords318.columns,Matrix.one_apply,Pi.single_apply,eq_comm] using h
end VaryingNormalizedWordFrame318
