module
public import ActualTwoDescentOriginalOverlapInjectivity318
public section
noncomputable section
namespace ActualTwoDescentLocalizationFractionMaps318
open scoped nonZeroDivisors
variable (A S : Type*) [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
  (M : Submonoid A) [Algebra A S] [IsLocalization M S]
  (hAS : Function.Injective (algebraMap A S))

include S in
lemma actual_denominator_nonzero (m : M) : (m : A) ≠ 0 := by
  intro h
  apply (IsLocalization.map_units S m).ne_zero
  simp only [h,map_zero]

/-- Native localization into the ORIGINAL base fraction field. -/
def toBaseFraction : S →+* FractionRing A :=
  IsLocalization.lift (M:=M) (g:=algebraMap A (FractionRing A)) (fun m =>
    isUnit_iff_ne_zero.mpr (by
      intro h
      apply actual_denominator_nonzero A S M m
      apply IsFractionRing.injective A (FractionRing A)
      simpa only [map_zero] using h))

@[simp] lemma actual_to_base_fraction (a : A) :
    toBaseFraction A S M (algebraMap A S a)=algebraMap A (FractionRing A) a :=
  IsLocalization.lift_eq _ _

include hAS in
lemma actual_to_base_fraction_injective : Function.Injective (toBaseFraction A S M) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  constructor
  · intro h
    exact congrArg (algebraMap A (FractionRing A)) (hAS h)
  · intro h
    exact congrArg (algebraMap A S) (IsFractionRing.injective A (FractionRing A) h)

def fractionForward : FractionRing A →+* FractionRing S :=
  IsFractionRing.lift (g:=(algebraMap S (FractionRing S)).comp (algebraMap A S))
    ((IsFractionRing.injective S (FractionRing S)).comp hAS)
def fractionBackward : FractionRing S →+* FractionRing A :=
  IsFractionRing.lift (actual_to_base_fraction_injective A S M hAS)

@[simp] lemma actual_fraction_forward_base (a : A) :
    fractionForward A S hAS (algebraMap A (FractionRing A) a)=
      algebraMap S (FractionRing S) (algebraMap A S a) :=
  IsFractionRing.lift_algebraMap _ _
@[simp] lemma actual_fraction_backward_base (s : S) :
    fractionBackward A S M hAS (algebraMap S (FractionRing S) s)=toBaseFraction A S M s :=
  IsFractionRing.lift_algebraMap _ _
end ActualTwoDescentLocalizationFractionMaps318
