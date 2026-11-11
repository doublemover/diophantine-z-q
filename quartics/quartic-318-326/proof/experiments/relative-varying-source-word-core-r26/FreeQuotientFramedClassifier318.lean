module
public import CyclicQuotientCanonicalFrame318
public import VaryingSourceWordQuotient318
public import Mathlib.Algebra.Algebra.Equiv
public section
noncomputable section
namespace FreeQuotientFramedClassifier318
open CyclicQuotientEvaluation318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "V" => (ι → R)

structure Framed where
  action : A →ₐ[R] Module.End R V
  marked : V
  cyclic : Function.Surjective (evaluation action marked)

/-- The full ideal, with an existential basis of the specified finite
rank, is the actual affine free quotient object to be classified. -/
abbrev FreeIdeal := {I : Ideal A // Nonempty (Module.Basis ι R (A ⧸ I))}
@[expose] def toIdeal (d : Framed R A ι) : FreeIdeal R A ι :=
  ⟨ideal d.action d.marked,⟨CyclicQuotientKernel318.quotientBasis d.action d.marked
    (VaryingSourceWordQuotient318.standardBasis ι R) d.cyclic⟩⟩

@[expose] def frameRelation (d e : Framed R A ι) : Prop :=
  ∃ f : V ≃ₗ[R] V,
    (∀ a x, f (d.action a x)=e.action a (f x)) ∧ f d.marked=e.marked

lemma frameRelation_iff (d e : Framed R A ι) :
    frameRelation R A ι d e ↔ toIdeal R A ι d=toIdeal R A ι e := by
  rw [Subtype.ext_iff]
  exact (CyclicQuotientCanonicalFrame318.ideal_eq_iff_frame d.action e.action
    d.marked e.marked d.cyclic e.cyclic).symm

@[expose] def frameSetoid : Setoid (Framed R A ι) where
  r := frameRelation R A ι
  iseqv :=
    ⟨fun d => (frameRelation_iff R A ι d d).mpr rfl,
      fun h => (frameRelation_iff R A ι _ _).mpr ((frameRelation_iff R A ι _ _).mp h).symm,
      fun h₁ h₂ => (frameRelation_iff R A ι _ _).mpr
        (((frameRelation_iff R A ι _ _).mp h₁).trans ((frameRelation_iff R A ι _ _).mp h₂))⟩

variable (I : Ideal A) (b : Module.Basis ι R (A ⧸ I))
local notation "q" => Ideal.Quotient.mkₐ R I
local notation "ρ" => OriginalFreeQuotientAction318.action q
@[expose] def fromBasis : Framed R A ι where
  action := (b.equivFun.conjAlgEquiv R).toAlgHom.comp ρ
  marked := b.equivFun 1
  cyclic := CyclicQuotientIntertwiner318.cyclic_transport ρ
    ((b.equivFun.conjAlgEquiv R).toAlgHom.comp ρ) 1 (b.equivFun 1) b.equivFun
    (fun a x => by
      change b.equivFun (ρ a x)=b.equivFun (ρ a (b.equivFun.symm (b.equivFun x)))
      rw [LinearEquiv.symm_apply_apply]) rfl
    (OriginalFreeQuotientAction318.cyclic q Ideal.Quotient.mk_surjective)

lemma fromBasis_ideal : (toIdeal R A ι (fromBasis R A ι I b)).val=I := by
  have hi := CyclicQuotientIntertwiner318.ideal_eq ρ
    ((b.equivFun.conjAlgEquiv R).toAlgHom.comp ρ) 1 (b.equivFun 1) b.equivFun
    (fun a x => by
      change b.equivFun (ρ a x)=b.equivFun (ρ a (b.equivFun.symm (b.equivFun x)))
      rw [LinearEquiv.symm_apply_apply]) rfl
  change ideal ((b.equivFun.conjAlgEquiv R).toAlgHom.comp ρ) (b.equivFun 1)=I
  rw [← hi,OriginalFreeQuotientAction318.ideal_eq_kernel]
  ext a
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Every free ideal quotient has an actual cyclic framed representative. -/
lemma toIdeal_surjective : Function.Surjective (toIdeal R A ι) := by
  rintro ⟨I,⟨b⟩⟩
  refine ⟨fromBasis R A ι I b,?_⟩
  apply Subtype.ext
  exact fromBasis_ideal R A ι I b

/-- The set quotient is by ACTUAL invertible action/vector frame changes.
This all-ring classifier alone is not a represented scheme quotient. -/
@[expose] def classifier : Quotient (frameSetoid R A ι) ≃ FreeIdeal R A ι :=
  Equiv.ofBijective
    (Quotient.lift (toIdeal R A ι) (fun _ _ h => (frameRelation_iff R A ι _ _).mp h))
    ⟨by
      intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro d e h
      exact Quotient.sound ((frameRelation_iff R A ι d e).mpr h),by
      intro I
      obtain ⟨d,hd⟩ := toIdeal_surjective R A ι I
      exact ⟨Quotient.mk _ d,hd⟩⟩
end FreeQuotientFramedClassifier318
