module
public import CyclicWordNormalization318
public section
noncomputable section
namespace CyclicNormalizedFrameUniqueness318
open CyclicQuotientEvaluation318 FreeQuotientFramedClassifier318
open CyclicQuotientCanonicalFrame318 CyclicWordNormalization318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (d e : Framed R A ι) (w : ι → A)

/-- A normalized word frame has no residual frame ambiguity. Equality
of the original full ideals forces equality of the entire action/vector. -/
lemma eq_of_ideal (hd : Normalized R A ι d w) (he : Normalized R A ι e w)
    (h : toIdeal R A ι d=toIdeal R A ι e) : d=e := by
  have hI : ideal d.action d.marked=ideal e.action e.marked := congrArg Subtype.val h
  let f := equiv d.action e.action d.marked e.marked d.cyclic e.cyclic hI
  have hf : f=LinearEquiv.refl R (ι → R) := by
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun R ι).ext
    intro j
    change f (Pi.single j 1)=Pi.single j 1
    calc
      f (Pi.single j 1)=f (evaluation d.action d.marked (w j)) := congrArg f (hd j).symm
      _=evaluation e.action e.marked (w j) :=
        equiv_evaluation d.action e.action d.marked e.marked d.cyclic e.cyclic hI (w j)
      _=Pi.single j 1 := he j
  have hm : d.action=e.action := by
    apply AlgHom.ext
    intro a
    apply LinearMap.ext
    intro x
    have hx := equiv_intertwines d.action e.action d.marked e.marked
      d.cyclic e.cyclic hI a x
    change f (d.action a x)=e.action a (f x) at hx
    simpa only [hf,LinearEquiv.refl_apply] using hx
  have hv : d.marked=e.marked := by
    have hx := equiv_marked d.action e.action d.marked e.marked d.cyclic e.cyclic hI
    change f d.marked=e.marked at hx
    simpa only [hf,LinearEquiv.refl_apply] using hx
  cases d
  cases e
  cases hm
  cases hv
  rfl

/-- Normalizing two equivalent frames at the same words yields identical
coordinates. This is equality over the whole ring, including nilpotents. -/
lemma normalize_eq (hI : toIdeal R A ι d=toIdeal R A ι e)
    (hd : IsUnit (columns R A ι d w).det) (he : IsUnit (columns R A ι e w).det) :
    normalize R A ι d w hd=normalize R A ι e w he :=
  eq_of_ideal R A ι _ _ w (normalize_is_normalized R A ι d w hd)
    (normalize_is_normalized R A ι e w he)
    ((normalize_ideal R A ι d w hd).trans (hI.trans (normalize_ideal R A ι e w he).symm))
end CyclicNormalizedFrameUniqueness318
