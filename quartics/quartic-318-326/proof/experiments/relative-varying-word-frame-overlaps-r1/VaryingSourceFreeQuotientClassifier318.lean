module
public import FreeQuotientFramedClassifier318
public import VaryingSourceGlobalWordCover318
public section
noncomputable section
namespace VaryingSourceFreeQuotientClassifier318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
local notation "B" => (S ⊗[R] A)
local notation "V" => (ι → S)

structure Cyclic where
  data : Action R A ι S
  cyclic : Function.Surjective (evaluation (linearAction R A ι S data) data.marked)
private lemma action_ext {a b : Action R A ι S}
    (hm : a.map=b.map) (hv : a.marked=b.marked) : a=b := by
  cases a
  cases b
  cases hm
  cases hv
  rfl
private lemma cyclic_ext {a b : Cyclic R A ι S} (h : a.data=b.data) : a=b := by
  cases a
  cases b
  cases h
  rfl
private lemma framed_ext {a b : FreeQuotientFramedClassifier318.Framed S B ι}
    (hm : a.action=b.action) (hv : a.marked=b.marked) : a=b := by
  cases a
  cases b
  cases hm
  cases hv
  rfl

@[expose] def toFramed (a : Cyclic R A ι S) : FreeQuotientFramedClassifier318.Framed S B ι :=
  ⟨linearAction R A ι S a.data,a.data.marked,a.cyclic⟩

/-- Recover the original-source matrices by the inverse of the SAME
scalar-extension adjunction, retaining the actual tensor action. -/
@[expose] def fromFramedData (d : FreeQuotientFramedClassifier318.Framed S B ι) : Action R A ι S :=
  ⟨(AlgHom.liftEquiv R S A (Matrix ι ι S)).symm
    (LinearMap.toMatrixAlgEquiv'.toAlgHom.comp d.action),d.marked⟩

lemma fromFramed_action (d : FreeQuotientFramedClassifier318.Framed S B ι) :
    linearAction R A ι S (fromFramedData R A ι S d)=d.action := by
  change Matrix.toLinAlgEquiv'.toAlgHom.comp
    ((AlgHom.liftEquiv R S A (Matrix ι ι S))
      ((AlgHom.liftEquiv R S A (Matrix ι ι S)).symm
        (LinearMap.toMatrixAlgEquiv'.toAlgHom.comp d.action)))=d.action
  rw [Equiv.apply_symm_apply]
  apply AlgHom.ext
  intro z
  exact Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (d.action z)

@[expose] def fromFramed (d : FreeQuotientFramedClassifier318.Framed S B ι) : Cyclic R A ι S :=
  ⟨fromFramedData R A ι S d,by
    rw [fromFramed_action]
    exact d.cyclic⟩

lemma from_to_data (a : Cyclic R A ι S) :
    fromFramedData R A ι S (toFramed R A ι S a)=a.data := by
  have hm : (fromFramedData R A ι S (toFramed R A ι S a)).map=a.data.map := by
    change (AlgHom.liftEquiv R S A (Matrix ι ι S)).symm
      (LinearMap.toMatrixAlgEquiv'.toAlgHom.comp
        (Matrix.toLinAlgEquiv'.toAlgHom.comp (matrixAction R A ι S a.data)))=a.data.map
    have h : LinearMap.toMatrixAlgEquiv'.toAlgHom.comp
        (Matrix.toLinAlgEquiv'.toAlgHom.comp (matrixAction R A ι S a.data))=
        matrixAction R A ι S a.data := by
      apply AlgHom.ext
      intro z
      exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' (matrixAction R A ι S a.data z)
    rw [h]
    exact (AlgHom.liftEquiv R S A (Matrix ι ι S)).symm_apply_apply a.data.map
  have hv : (fromFramedData R A ι S (toFramed R A ι S a)).marked=a.data.marked := rfl
  exact action_ext R A ι S hm hv

/-- A two-sided equivalence between genuine cyclic source actions and
cyclic actions of the literal S tensor A. No quotient has been changed. -/
@[expose] def framedEquiv : Cyclic R A ι S ≃ FreeQuotientFramedClassifier318.Framed S B ι where
  toFun := toFramed R A ι S
  invFun := fromFramed R A ι S
  left_inv a := by
    apply cyclic_ext R A ι S
    exact from_to_data R A ι S a
  right_inv d := by
    apply framed_ext R A ι S
    · exact fromFramed_action R A ι S d
    · rfl

/-- Every free quotient of the original base-changed source is recovered
by an actual source action. Combined with frameRelation_iff, the fibres
are exactly invertible action/vector frame changes, not radical ideals. -/
lemma source_ideal_surjective : Function.Surjective
    (fun a : Cyclic R A ι S => FreeQuotientFramedClassifier318.toIdeal S B ι
      (toFramed R A ι S a)) :=
  (FreeQuotientFramedClassifier318.toIdeal_surjective S B ι).comp
    (framedEquiv R A ι S).surjective
end VaryingSourceFreeQuotientClassifier318
