module
public import ActualTwoDescentLocalizationFractionMaps318
public section
noncomputable section
namespace ActualTwoDescentLocalizationFractionEquivalence318
open ActualTwoDescentLocalizationFractionMaps318
variable (A S : Type*) [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
  (M : Submonoid A) [Algebra A S] [IsLocalization M S]
  (hAS : Function.Injective (algebraMap A S))

lemma actual_fraction_left_inverse :
    (fractionBackward A S M hAS).comp (fractionForward A S hAS)=RingHom.id (FractionRing A) := by
  apply IsFractionRing.ringHom_ext (A:=A)
  intro a
  change fractionBackward A S M hAS (fractionForward A S hAS (algebraMap A (FractionRing A) a))=_
  rw [actual_fraction_forward_base,actual_fraction_backward_base,actual_to_base_fraction]
  rfl

lemma actual_fraction_forward_local :
    (fractionForward A S hAS).comp (toBaseFraction A S M)=algebraMap S (FractionRing S) := by
  apply IsLocalization.ringHom_ext M
  ext a
  change fractionForward A S hAS (toBaseFraction A S M (algebraMap A S a))=_
  rw [actual_to_base_fraction,actual_fraction_forward_base]
  rfl

lemma actual_fraction_right_inverse :
    (fractionForward A S hAS).comp (fractionBackward A S M hAS)=RingHom.id (FractionRing S) := by
  apply IsFractionRing.ringHom_ext (A:=S)
  intro s
  change fractionForward A S hAS (fractionBackward A S M hAS (algebraMap S (FractionRing S) s))=_
  rw [actual_fraction_backward_base]
  exact DFunLike.congr_fun (actual_fraction_forward_local A S M hAS) s

/-- Native fraction fields before and after a specified injective
localization, with both exact map identities produced. -/
def localizationFractionEquiv : FractionRing A ≃+* FractionRing S where
  toFun := fractionForward A S hAS
  invFun := fractionBackward A S M hAS
  left_inv x := DFunLike.congr_fun (actual_fraction_left_inverse A S M hAS) x
  right_inv x := DFunLike.congr_fun (actual_fraction_right_inverse A S M hAS) x
  map_mul' := (fractionForward A S hAS).map_mul
  map_add' := (fractionForward A S hAS).map_add

@[simp] lemma actual_localization_fraction_equiv_base (a : A) :
    localizationFractionEquiv A S M hAS (algebraMap A (FractionRing A) a)=
      algebraMap S (FractionRing S) (algebraMap A S a) :=
  actual_fraction_forward_base A S hAS a
end ActualTwoDescentLocalizationFractionEquivalence318
