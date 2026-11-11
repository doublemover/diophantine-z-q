module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace AffineQuotientPushout318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {B C : CommRingCat.{u}} (f : B ⟶ C) (I : Ideal B) (J : Ideal C)
  (h : I.map f.hom=J)
abbrev source := CommRingCat.of (B ⧸ I)
abbrev target := CommRingCat.of (C ⧸ J)
@[expose] def sourceMap : B ⟶ source I := CommRingCat.ofHom (Ideal.Quotient.mk I)
@[expose] def targetMap : C ⟶ target J := CommRingCat.ofHom (Ideal.Quotient.mk J)
@[expose] def arrow : source I ⟶ target J :=
  CommRingCat.ofHom (Ideal.quotientMap J f.hom (Ideal.map_le_iff_le_comap.mp h.le))
lemma arrow_mk (b : B) : (arrow f I J h).hom (Ideal.Quotient.mk I b)=
    Ideal.Quotient.mk J (f.hom b) := rfl
lemma square : f ≫ targetMap J=sourceMap I ≫ arrow f I J h := by
  apply CommRingCat.hom_ext
  ext b
  rfl

/-- Arbitrary base change of an affine closed quotient is the quotient
by the actual extended ideal. No flatness or reducedness is assumed. -/
lemma pushout : IsPushout f (sourceMap I) (targetMap J) (arrow f I J h) := by
  let descend (s : PushoutCocone f (sourceMap I)) : target J ⟶ s.pt :=
    CommRingCat.ofHom (Ideal.Quotient.lift J s.inl.hom (by
      have hk : J ≤ RingHom.ker s.inl.hom := by
        rw [← h]
        apply Ideal.map_le_iff_le_comap.mpr
        intro b hb
        change s.inl.hom (f.hom b)=0
        have he := congrArg (fun k : B ⟶ s.pt => k.hom b) s.condition
        change s.inl.hom (f.hom b)=s.inr.hom (Ideal.Quotient.mk I b) at he
        rw [he,Ideal.Quotient.eq_zero_iff_mem.mpr hb,map_zero]
      exact fun b hb => hk hb))
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (targetMap J) (arrow f I J h) (square f I J h))
  refine PushoutCocone.IsColimit.mk (square f I J h) descend ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    ext c
    exact Ideal.Quotient.lift_mk _ _ _
  · intro s
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective z
    change (descend s).hom ((arrow f I J h).hom (Ideal.Quotient.mk I b))=
      s.inr.hom (Ideal.Quotient.mk I b)
    rw [arrow_mk]
    change Ideal.Quotient.lift J s.inl.hom _ (Ideal.Quotient.mk J (f.hom b))=_
    rw [Ideal.Quotient.lift_mk]
    exact congrArg (fun k : B ⟶ s.pt => k.hom b) s.condition
  · intro s m hm _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective z
    have he := congrArg (fun k : C ⟶ s.pt => k.hom c) hm
    exact he.trans (Ideal.Quotient.lift_mk _ _ _).symm

lemma pullback : IsPullback (Spec.map (targetMap J)) (Spec.map (arrow f I J h))
    (Spec.map f) (Spec.map (sourceMap I)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (pushout f I J h)
end AffineQuotientPushout318
