module
public import VaryingWordOverlapSelf318
public section
noncomputable section
namespace VaryingWordTriplePoints318
open VaryingNormalizedWordOverlap318 VaryingNormalizedOverlapFrames318
open VaryingWordTransitionNaturality318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S]
local notation "B" => (S ⊗[R] A)
local notation "words" t => (fun j => (1 : S) ⊗ₜ[R] (t j).prod)

abbrev Point := {d : VaryingNormalizedWordOverlap318.Point R A ι w S v //
  IsUnit (VaryingMatrixWords318.determinant d.val.val.val u)}

lemma frame_transition (d : VaryingNormalizedWordOverlap318.Point R A ι w S v) :
    (VaryingNormalizedFrameEquiv318.toFrame R A ι v S (transition R A ι w S v d).val).val=
      CyclicWordNormalization318.normalize S B ι
        (VaryingNormalizedFrameEquiv318.toFrame R A ι w S d.val).val (words v)
          (toFrames R A ι w S v d).property := by
  have h := (overlapFrames R A ι v S w).apply_symm_apply
    (CyclicWordFrameOverlap318.transition S B ι (words w) (words v)
      (overlapFrames R A ι w S v d))
  exact congrArg (fun e : OverlapFrames R A ι v S w => e.val.val) h

lemma third_unit (d : Point R A ι w v u S) :
    IsUnit (VaryingMatrixWords318.determinant
      (transition R A ι w S v d.val).val.val.val u) := by
  change IsUnit (VaryingMatrixWords318.columns
    (transition R A ι w S v d.val).val.val.val u).det
  rw [← frame_columns,frame_transition R A ι w v S]
  apply CyclicWordFrameOverlap318.unit_after_normalize
  rw [frame_columns]
  exact d.property

/-- Rotate (w;v,u) to (v;u,w) using the actual inverse v-word frame. -/
@[expose] def rotate (d : Point R A ι w v u S) : Point R A ι v u w S :=
  ⟨⟨(transition R A ι w S v d.val).val,third_unit R A ι w v u S d⟩,
    (transition R A ι w S v d.val).property⟩

@[expose] def second (d : Point R A ι w v u S) :
    VaryingNormalizedWordOverlap318.Point R A ι w S u := ⟨d.val.val,d.property⟩
lemma rotate_leg (d : Point R A ι w v u S) :
    second R A ι v u w S (rotate R A ι w v u S d)=transition R A ι w S v d.val := rfl

@[expose] def frame (d : Point R A ι w v u S) :=
  VaryingNormalizedFrameEquiv318.toFrame R A ι w S d.val.val
lemma rotate_ideal (d : Point R A ι w v u S) :
    FreeQuotientFramedClassifier318.toIdeal S B ι (frame R A ι v u w S (rotate R A ι w v u S d)).val=
      FreeQuotientFramedClassifier318.toIdeal S B ι (frame R A ι w v u S d).val := by
  change FreeQuotientFramedClassifier318.toIdeal S B ι
    (VaryingNormalizedFrameEquiv318.toFrame R A ι v S (transition R A ι w S v d.val).val).val=_
  rw [frame_transition R A ι w v S]
  exact CyclicWordNormalization318.normalize_ideal S B ι _ _ _

lemma rotate_cycle (d : Point R A ι w v u S) :
    rotate R A ι u w v S (rotate R A ι v u w S (rotate R A ι w v u S d))=d := by
  apply Subtype.ext
  apply Subtype.ext
  apply (VaryingNormalizedFrameEquiv318.frames R A ι w S).injective
  apply Subtype.ext
  apply CyclicNormalizedFrameUniqueness318.eq_of_ideal S B ι _ _ (words w)
    (frame R A ι w v u S
      (rotate R A ι u w v S (rotate R A ι v u w S (rotate R A ι w v u S d)))).property
    (frame R A ι w v u S d).property
  exact (rotate_ideal R A ι u w v S _).trans
    ((rotate_ideal R A ι v u w S _).trans (rotate_ideal R A ι w v u S d))

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
@[expose] def mapPoint (d : Point R A ι w v u S) : Point R A ι w v u T :=
  ⟨VaryingNormalizedWordOverlap318.mapPoint R A ι w S v T f d.val,by
    rw [← VaryingNormalizedWordNaturality318.determinant_map]
    exact d.property.map f.toMonoidHom⟩
lemma rotate_natural (d : Point R A ι w v u S) :
    mapPoint R A ι v u w S T f (rotate R A ι w v u S d)=
      rotate R A ι w v u T (mapPoint R A ι w v u S T f d) := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val (transition_natural R A ι w S v T f d.val)
end VaryingWordTriplePoints318
