module
public import VaryingProjectiveQuotientEquiv318
public section
noncomputable section
namespace VaryingProjectiveQuotientNaturality318
open VaryingProjectiveQuotientEquiv318
open scoped TensorProduct
universe u
variable (R A ι S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
  (f : S →ₐ[R] T)
/-- Arbitrary coefficient extension retains finite projectivity and the
intended constant rank on the literal extended quotient ideal. -/
@[expose] def mapIdeal (I : ProjectiveIdeal R A ι S) : ProjectiveIdeal R A ι T :=
  fromLocal R A ι T (VaryingLocalFreeQuotientNaturality318.mapIdeal R A ι S T f (toLocal R A ι S I))
lemma mapIdeal_val (I : ProjectiveIdeal R A ι S) : (mapIdeal R A ι S T f I).val=
    I.val.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom := rfl
lemma classify_natural (I : ProjectiveIdeal R A ι S) :
    equivalence R A ι T (mapIdeal R A ι S T f I)=
      VaryingParameterPoint318.map R A ι S T f (equivalence R A ι S I) := by
  have h : toLocal R A ι T (mapIdeal R A ι S T f I)=
      VaryingLocalFreeQuotientNaturality318.mapIdeal R A ι S T f (toLocal R A ι S I) :=
    Subtype.ext rfl
  change VaryingLocalFreeQuotientEquiv318.classify R A ι T
    (toLocal R A ι T (mapIdeal R A ι S T f I))=_
  rw [h]
  exact VaryingLocalFreeQuotientNaturality318.classify_natural R A ι S T f (toLocal R A ι S I)
lemma recover_natural (x : VaryingParameterPoint318.Point R A ι S) :
    (equivalence R A ι T).symm (VaryingParameterPoint318.map R A ι S T f x)=
      mapIdeal R A ι S T f ((equivalence R A ι S).symm x) := by
  apply Subtype.ext
  exact VaryingPointIdealNaturality318.ideal_map R A ι S T f x
end VaryingProjectiveQuotientNaturality318
