module
public import IntegralOriginalRootCoordinates318
public section
noncomputable section
namespace IntegralRationalInfinityCoordinate318
open IntegralSourceBranches318 IntegralBranchCoordinates318
open IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318 IntegralInfinityCommonBase318
open IntegralRationalFullOverlap318 IntegralOriginalRootCoordinates318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (InfinityFieldCoordinates318.L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- Ordered-root compatibility fixes the sign of y0 in the original field. -/
theorem root_zero :
    originalFieldEmbedding c (commonMap ℚ c (rootUnit ℚ c : CommonBase ℚ c)) =
      InfinityFieldCoordinates318.root c 0 := by
  rw [←finite_coordinate,coordinate_eq_root]
  change originalFieldEmbedding c
    (sourceMap ℚ c (IntegralOriginalRootCoordinates318.root ℚ c 0)) = _
  rw [originalFieldEmbedding_source,rational_root,ContactRootReciprocals318.embedding_root]

/-- The original reciprocal coordinate is identified with c0/y0 using the
signed original root, not inferred from u²=c0/t. -/
theorem reciprocal_coordinate :
    originalFieldEmbedding c (infinityMap ℚ c (IntegralInfinityChart318.coordinate ℚ c)) =
      InfinityFieldCoordinates318.u c := by
  rw [infinity_coordinate]
  have h := congrArg ((originalFieldEmbedding c).comp (commonMap ℚ c).toRingHom)
    (reciprocal_relation ℚ c)
  simp only [RingHom.comp_apply,map_mul,AlgHom.commutes,RingHom.map_rat_algebraMap,map_one,root_zero] at h
  change _ = algebraMap ℚ (InfinityFieldCoordinates318.L c) (c 0 : ℚ) /
    InfinityFieldCoordinates318.root c 0
  apply (eq_div_iff (InfinityFieldCoordinates318.root_ne_zero c 0)).mpr
  exact (mul_comm _ _).trans h
end IntegralRationalInfinityCoordinate318
