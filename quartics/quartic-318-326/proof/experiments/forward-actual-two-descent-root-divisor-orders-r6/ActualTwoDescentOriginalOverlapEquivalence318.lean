module
public import ActualTwoDescentOriginalOverlapLocalizationMaps318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapEquivalence318
open Polynomial ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
open ActualTwoDescentOriginalOverlapLocalizationMaps318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_affine_overlap_left_inverse (n : K) :
    (infinityOverlapMap n).comp (affineOverlapMap n)=RingHom.id (AffinePuncture n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (affineY n))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · ext a
      change infinityOverlapMap n (affineOverlapMap n (affineOpenCoefficient n a))=
        affineOpenCoefficient n a
      simp
    · change infinityOverlapMap n (affineOverlapMap n (openX n))=openX n
      rw [actual_affine_overlap_x,map_mul,actual_infinity_overlap_u,
        actual_infinity_overlap_inverse_v]
      calc
        (openX n*inverseY n)*openY n=openX n*(openY n*inverseY n) := by ring
        _=openX n := by rw [actual_open_y_inverse,mul_one]
  · change infinityOverlapMap n (affineOverlapMap n (openY n))=openY n
    simp

lemma actual_infinity_overlap_right_inverse (n : K) :
    (affineOverlapMap n).comp (infinityOverlapMap n)=RingHom.id (InfinityPuncture n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (chartV n))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · ext a
      change affineOverlapMap n (infinityOverlapMap n (infinityOpenCoefficient n a))=
        infinityOpenCoefficient n a
      simp
    · change affineOverlapMap n (infinityOverlapMap n (openU n))=openU n
      rw [actual_infinity_overlap_u,map_mul,actual_affine_overlap_x,
        actual_affine_overlap_inverse_y]
      calc
        (openU n*inverseV n)*openV n=openU n*(openV n*inverseV n) := by ring
        _=openU n := by rw [actual_open_v_inverse,mul_one]
  · change affineOverlapMap n (infinityOverlapMap n (openV n))=openV n
    simp

/-- Actual punctured-chart ring equivalence for the ORIGINAL curve.
Both inverse laws hold on all localized elements, not only points. -/
def originalOverlapEquiv (n : K) : AffinePuncture n ≃+* InfinityPuncture n where
  toFun := affineOverlapMap n
  invFun := infinityOverlapMap n
  left_inv x := DFunLike.congr_fun (actual_affine_overlap_left_inverse n) x
  right_inv x := DFunLike.congr_fun (actual_infinity_overlap_right_inverse n) x
  map_mul' := (affineOverlapMap n).map_mul
  map_add' := (affineOverlapMap n).map_add
end ActualTwoDescentOriginalOverlapEquivalence318
