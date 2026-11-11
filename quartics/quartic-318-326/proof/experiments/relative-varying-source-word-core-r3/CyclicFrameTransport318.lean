module
public import FreeQuotientFramedClassifier318
public section
noncomputable section
namespace CyclicFrameTransport318
open CyclicQuotientEvaluation318 FreeQuotientFramedClassifier318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (d : Framed R A ι) (e : (ι → R) ≃ₗ[R] (ι → R))

@[expose] def changeFrame : Framed R A ι where
  action := (e.conjAlgEquiv R).toAlgHom.comp d.action
  marked := e d.marked
  cyclic := CyclicQuotientIntertwiner318.cyclic_transport d.action
    ((e.conjAlgEquiv R).toAlgHom.comp d.action) d.marked (e d.marked) e
    (fun a x => by
      change e (d.action a x)=e (d.action a (e.symm (e x)))
      rw [LinearEquiv.symm_apply_apply]) rfl d.cyclic

lemma intertwines (a : A) (x : ι → R) :
    e (d.action a x)=(changeFrame R A ι d e).action a (e x) := by
  change e (d.action a x)=e (d.action a (e.symm (e x)))
  rw [LinearEquiv.symm_apply_apply]
lemma evaluation_change (a : A) :
    evaluation (changeFrame R A ι d e).action (changeFrame R A ι d e).marked a=
      e (evaluation d.action d.marked a) :=
  (CyclicQuotientIntertwiner318.evaluation_intertwines d.action
    (changeFrame R A ι d e).action d.marked (e d.marked) e
    (intertwines R A ι d e) rfl a).symm
lemma ideal_change : toIdeal R A ι (changeFrame R A ι d e)=toIdeal R A ι d := by
  apply Subtype.ext
  exact (CyclicQuotientIntertwiner318.ideal_eq d.action (changeFrame R A ι d e).action
    d.marked (e d.marked) e (intertwines R A ι d e) rfl).symm
end CyclicFrameTransport318
