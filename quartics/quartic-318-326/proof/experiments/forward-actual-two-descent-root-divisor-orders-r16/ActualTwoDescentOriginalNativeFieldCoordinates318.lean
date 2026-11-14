module
public import ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
public section
noncomputable section
namespace ActualTwoDescentOriginalNativeFieldCoordinates318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeFractionFunctions318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
open ActualTwoDescentOriginalOverlapLocalizationMaps318 ActualTwoDescentOriginalOverlapEquivalence318
open ActualTwoDescentOriginalOverlapInjectivity318 ActualTwoDescentLocalizationFractionEquivalence318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
variable {K : Type*} [Field K] [CharZero K]

@[simp] lemma actual_affine_fraction_open_base (n : K) (a : AffineChart n) :
    affineFractionOpenEquiv n (algebraMap (AffineChart n) _ a)=
      algebraMap (AffinePuncture n) _ (affineOpenMap n a) :=
  actual_localization_fraction_equiv_base _ _ _ _ a
@[simp] lemma actual_punctured_fraction_base (n : K) (a : AffinePuncture n) :
    puncturedFractionEquiv n (algebraMap (AffinePuncture n) _ a)=
      algebraMap (InfinityPuncture n) _ (affineOverlapMap n a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a
@[simp] lemma actual_infinity_fraction_open_base (n : K) (a : InfinityChart n) :
    infinityFractionOpenEquiv n (algebraMap (InfinityChart n) _ a)=
      algebraMap (InfinityPuncture n) _ (infinityOpenMap n a) :=
  actual_localization_fraction_equiv_base _ _ _ _ a
@[simp] lemma actual_infinity_fraction_open_inverse_base (n : K) (a : InfinityChart n) :
    (infinityFractionOpenEquiv n).symm
      (algebraMap (InfinityPuncture n) _ (infinityOpenMap n a))=
        algebraMap (InfinityChart n) _ a := by
  apply (infinityFractionOpenEquiv n).injective
  rw [RingEquiv.apply_symm_apply,actual_infinity_fraction_open_base]
@[simp] lemma actual_infinity_fraction_local_base (n : K) (a : InfinityChart n) :
    infinityFractionLocalEquiv n (algebraMap (InfinityChart n) _ a)=
      infinityFractionMap n (algebraMap (InfinityChart n) (InfinityLocalRing n) a) :=
  actual_localization_fraction_equiv_base _ _ _ _ a

lemma actual_inverse_v_fraction (n : K) :
    algebraMap (InfinityPuncture n) (FractionRing (InfinityPuncture n)) (inverseV n)=
      (algebraMap (InfinityPuncture n) (FractionRing (InfinityPuncture n)) (openV n))⁻¹ := by
  have hv : algebraMap (InfinityPuncture n) (FractionRing (InfinityPuncture n)) (openV n) ≠ 0 := by
    intro h
    have h' : openV n=0 := by
      apply IsFractionRing.injective (InfinityPuncture n) (FractionRing (InfinityPuncture n))
      simpa only [map_zero] using h
    apply ActualTwoDescentInfinityNativeDomain318.actual_chart_v_nonzero n
    apply actual_infinity_open_injective n
    simpa only [map_zero] using h'
  apply actual_inverse_unique
    (algebraMap (InfinityPuncture n) (FractionRing (InfinityPuncture n)) (openV n))
  · rw [←map_mul,actual_open_v_inverse,map_one]
  · exact mul_inv_cancel₀ hv

lemma actual_original_field_base (n : K) (a : AffineChart n) :
    originalNativeFunctionFieldEquiv n (algebraMap (AffineChart n) _ a)=
      infinityFractionLocalEquiv n ((infinityFractionOpenEquiv n).symm
        (algebraMap (InfinityPuncture n) _ (affineToInfinity n a))) := by
  simp only [originalNativeFunctionFieldEquiv,RingEquiv.trans_apply,
    actual_affine_fraction_open_base,actual_punctured_fraction_base,actual_affine_overlap_base]

lemma actual_original_field_x (n : K) :
    originalNativeFunctionFieldEquiv n (algebraMap (AffineChart n) _ (affineX n))=infinityAffineX n := by
  rw [actual_original_field_base,actual_affine_to_infinity_x,map_mul,actual_inverse_v_fraction,
    map_mul,map_inv₀]
  change infinityFractionLocalEquiv n
    ((infinityFractionOpenEquiv n).symm (algebraMap (InfinityPuncture n) _ (infinityOpenMap n (chartU n))) *
      ((infinityFractionOpenEquiv n).symm (algebraMap (InfinityPuncture n) _ (infinityOpenMap n (chartV n))))⁻¹)=_
  rw [actual_infinity_fraction_open_inverse_base,actual_infinity_fraction_open_inverse_base,
    map_mul,map_inv₀,actual_infinity_fraction_local_base,actual_infinity_fraction_local_base]
  rfl

lemma actual_original_field_y (n : K) :
    originalNativeFunctionFieldEquiv n (algebraMap (AffineChart n) _ (affineY n))=infinityAffineY n := by
  rw [actual_original_field_base,actual_affine_to_infinity_y,actual_inverse_v_fraction,map_inv₀]
  change infinityFractionLocalEquiv n
    (((infinityFractionOpenEquiv n).symm
      (algebraMap (InfinityPuncture n) _ (infinityOpenMap n (chartV n))))⁻¹)=_
  rw [actual_infinity_fraction_open_inverse_base,map_inv₀,actual_infinity_fraction_local_base]
  simp only [infinityAffineY,one_div,localV]

lemma actual_original_field_coefficient (n a : K) :
    originalNativeFunctionFieldEquiv n (algebraMap (AffineChart n) _ (affineCoefficient n a))=
      infinityFractionMap n (localCoefficient n a) := by
  rw [actual_original_field_base,actual_affine_to_infinity_coefficient]
  change infinityFractionLocalEquiv n ((infinityFractionOpenEquiv n).symm
    (algebraMap (InfinityPuncture n) _ (infinityOpenMap n (chartCoefficient n a))))=_
  rw [actual_infinity_fraction_open_inverse_base,actual_infinity_fraction_local_base]
  rfl
end ActualTwoDescentOriginalNativeFieldCoordinates318
