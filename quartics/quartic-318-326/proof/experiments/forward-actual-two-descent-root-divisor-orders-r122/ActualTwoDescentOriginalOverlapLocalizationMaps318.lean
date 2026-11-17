module
public import ActualTwoDescentOriginalOverlapQuotientMaps318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapLocalizationMaps318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_inverse_v_unit (n : K) : IsUnit (inverseV n) :=
  ⟨Units.mkOfMulEqOne (inverseV n) (openV n) (by
    simpa only [mul_comm] using actual_open_v_inverse n),rfl⟩
lemma actual_inverse_y_unit (n : K) : IsUnit (inverseY n) :=
  ⟨Units.mkOfMulEqOne (inverseY n) (openY n) (by
    simpa only [mul_comm] using actual_open_y_inverse n),rfl⟩

def affineOverlapMap (n : K) : AffinePuncture n →+* InfinityPuncture n :=
  IsLocalization.Away.lift (affineY n) (g:=affineToInfinity n)
    (by rw [actual_affine_to_infinity_y]; exact actual_inverse_v_unit n)
def infinityOverlapMap (n : K) : InfinityPuncture n →+* AffinePuncture n :=
  IsLocalization.Away.lift (chartV n) (g:=infinityToAffine n)
    (by rw [actual_infinity_to_affine_v]; exact actual_inverse_y_unit n)

@[simp] lemma actual_affine_overlap_base (n : K) (x : AffineChart n) :
    affineOverlapMap n (affineOpenMap n x)=affineToInfinity n x :=
  IsLocalization.Away.lift_eq _ _ _
@[simp] lemma actual_infinity_overlap_base (n : K) (x : InfinityChart n) :
    infinityOverlapMap n (infinityOpenMap n x)=infinityToAffine n x :=
  IsLocalization.Away.lift_eq _ _ _
@[simp] lemma actual_affine_overlap_x (n : K) : affineOverlapMap n (openX n)=openU n*inverseV n := by
  change affineOverlapMap n (affineOpenMap n (affineX n))=_
  rw [actual_affine_overlap_base,actual_affine_to_infinity_x]
@[simp] lemma actual_affine_overlap_y (n : K) : affineOverlapMap n (openY n)=inverseV n := by
  change affineOverlapMap n (affineOpenMap n (affineY n))=_
  rw [actual_affine_overlap_base,actual_affine_to_infinity_y]
@[simp] lemma actual_infinity_overlap_u (n : K) : infinityOverlapMap n (openU n)=openX n*inverseY n := by
  change infinityOverlapMap n (infinityOpenMap n (chartU n))=_
  rw [actual_infinity_overlap_base,actual_infinity_to_affine_u]
@[simp] lemma actual_infinity_overlap_v (n : K) : infinityOverlapMap n (openV n)=inverseY n := by
  change infinityOverlapMap n (infinityOpenMap n (chartV n))=_
  rw [actual_infinity_overlap_base,actual_infinity_to_affine_v]
@[simp] lemma actual_affine_overlap_coefficient (n a : K) :
    affineOverlapMap n (affineOpenCoefficient n a)=infinityOpenCoefficient n a := by
  change affineOverlapMap n (affineOpenMap n (affineCoefficient n a))=_
  rw [actual_affine_overlap_base,actual_affine_to_infinity_coefficient]
@[simp] lemma actual_infinity_overlap_coefficient (n a : K) :
    infinityOverlapMap n (infinityOpenCoefficient n a)=affineOpenCoefficient n a := by
  change infinityOverlapMap n (infinityOpenMap n (chartCoefficient n a))=_
  rw [actual_infinity_overlap_base,actual_infinity_to_affine_coefficient]

@[simp] lemma actual_affine_overlap_inverse_y (n : K) :
    affineOverlapMap n (inverseY n)=openV n := by
  apply actual_inverse_unique (inverseV n)
  · have h := congrArg (affineOverlapMap n) (actual_open_y_inverse n)
    simpa only [map_mul,map_one,actual_affine_overlap_y] using h
  · simpa only [mul_comm] using actual_open_v_inverse n
@[simp] lemma actual_infinity_overlap_inverse_v (n : K) :
    infinityOverlapMap n (inverseV n)=openY n := by
  apply actual_inverse_unique (inverseY n)
  · have h := congrArg (infinityOverlapMap n) (actual_open_v_inverse n)
    simpa only [map_mul,map_one,actual_infinity_overlap_v] using h
  · simpa only [mul_comm] using actual_open_y_inverse n
end ActualTwoDescentOriginalOverlapLocalizationMaps318
