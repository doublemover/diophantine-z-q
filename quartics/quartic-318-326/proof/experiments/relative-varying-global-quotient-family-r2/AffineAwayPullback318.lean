module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace AffineAwayPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {A B : CommRingCat.{u}} (f : A ⟶ B) (x : A)
abbrev source := CommRingCat.of (Localization.Away x)
abbrev target := CommRingCat.of (Localization.Away (f.hom x))
@[expose] def sourceMap : A ⟶ source x := CommRingCat.ofHom (algebraMap A (source x))
@[expose] def targetMap : B ⟶ target f x := CommRingCat.ofHom (algebraMap B (target f x))
@[expose] def arrow : source x ⟶ target f x :=
  CommRingCat.ofHom (IsLocalization.Away.lift x
    (show IsUnit (((algebraMap B (target f x)).comp f.hom) x) from
      IsLocalization.Away.algebraMap_isUnit (f.hom x)))
lemma arrow_base (a : A) : (arrow f x).hom (algebraMap A (source x) a)=
    algebraMap B (target f x) (f.hom a) := by
  simpa only [arrow,CommRingCat.hom_ofHom] using
    (IsLocalization.Away.lift_eq x
      (show IsUnit (((algebraMap B (target f x)).comp f.hom) x) from
        IsLocalization.Away.algebraMap_isUnit (f.hom x)) a)
lemma square : f ≫ targetMap f x=sourceMap x ≫ arrow f x := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (arrow_base f x a).symm

/-- Actual principal localization commutes with arbitrary base change.
This proof uses its ring universal property, not a reduced-point test. -/
lemma pushout : IsPushout f (sourceMap x) (targetMap f x) (arrow f x) := by
  let descend (s : PushoutCocone f (sourceMap x)) : target f x ⟶ s.pt :=
    CommRingCat.ofHom (IsLocalization.Away.lift (f.hom x)
      (show IsUnit (s.inl.hom (f.hom x)) from by
        have he := congrArg (fun k : A ⟶ s.pt => k.hom x) s.condition
        change s.inl.hom (f.hom x)=s.inr.hom (algebraMap A (source x) x) at he
        rw [he]
        exact (IsLocalization.Away.algebraMap_isUnit x).map s.inr.hom))
  apply IsPushout.of_isColimit (c := PushoutCocone.mk (targetMap f x) (arrow f x) (square f x))
  refine PushoutCocone.IsColimit.mk (square f x) descend ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact IsLocalization.Away.lift_eq _ _ b
  · intro s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers x)
    apply RingHom.ext
    intro a
    change (descend s).hom ((arrow f x).hom (algebraMap A (source x) a))=
      s.inr.hom (algebraMap A (source x) a)
    rw [arrow_base]
    change IsLocalization.Away.lift (f.hom x) _ (algebraMap B (target f x) (f.hom a))=_
    rw [IsLocalization.Away.lift_eq]
    exact congrArg (fun k : A ⟶ s.pt => k.hom a) s.condition
  · intro s m hm _
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (f.hom x))
    apply RingHom.ext
    intro b
    change m.hom (algebraMap B (target f x) b)=(descend s).hom (algebraMap B (target f x) b)
    have h := congrArg (fun k : B ⟶ s.pt => k.hom b) hm
    exact h.trans (IsLocalization.Away.lift_eq _ _ b).symm

lemma pullback : IsPullback (Spec.map (targetMap f x)) (Spec.map (arrow f x))
    (Spec.map f) (Spec.map (sourceMap x)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (pushout f x)
end AffineAwayPullback318
