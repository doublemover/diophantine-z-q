module
public import IntegralOtherRootCoordinates318
public import IntegralRationalInfinityCoordinate318
public import IntegralInfinityOriginalField318
public import InfinityOrderCoordinates318
public section
noncomputable section
namespace IntegralRationalInfinityMap318
open Polynomial
open IntegralOverlapChartMaps318 IntegralInfinityCommonBase318 IntegralOverlapRootGenerators318
open IntegralRationalFullOverlap318 IntegralOriginalRootCoordinates318 IntegralInfinityOriginalField318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (InfinityFieldCoordinates318.L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- Restrict the three actual integral infinity generators into the SAME
original field. Each is the original ordered quotient y_j/y0 with its sign. -/
theorem generator_original_field (j : Fin 3) :
    originalFieldEmbedding c (infinityMap ℚ c (infinityGenerator ℚ c j)) =
      InfinityFieldCoordinates318.ratio c j := by
  rw [infinityMap_generator,Algebra.smul_def,map_mul]
  have hunit : originalFieldEmbedding c
      (commonMap ℚ c (↑(rootUnit ℚ c)⁻¹ : CommonBase ℚ c)) =
        (InfinityFieldCoordinates318.root c 0)⁻¹ := by
    have h := congrArg ((originalFieldEmbedding c).comp (commonMap ℚ c).toRingHom)
      (Units.mul_inv (rootUnit ℚ c))
    simp only [RingHom.comp_apply,map_mul,map_one,IntegralRationalInfinityCoordinate318.root_zero] at h
    exact eq_inv_of_mul_eq_one_right h
  change originalFieldEmbedding c (commonMap ℚ c (↑(rootUnit ℚ c)⁻¹ : CommonBase ℚ c)) *
    originalFieldEmbedding c (1 ⊗ₜ[IntegralSourceBranches318.OpenBase ℚ c 0]
      finiteGenerator ℚ c j) = _
  rw [hunit,IntegralOtherRootCoordinates318.common_other,originalFieldEmbedding_source,
    rational_root,ContactRootReciprocals318.embedding_root]
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

theorem presentationEquiv_generator {a b : Fin 3 → ℚ[X]} (h : a=b) (j : Fin 3) :
    presentationEquiv h (ThreeRootCoordinates318.generator
      (fun i => algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3,a k)) (a i)) j) =
      ThreeRootCoordinates318.generator
        (fun i => algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3,b k)) (b i)) j := by
  subst b
  rfl

theorem rationalOrderEquiv_generator (j : Fin 3) :
    rationalOrderEquiv c (infinityGenerator ℚ c j) = InfinityOrderCoordinates318.generator c j :=
  presentationEquiv_generator (funext (IntegralInfinityCoefficients318.rational_coefficient c)) j

/-- Equality of the actual full infinity-order field embeddings, checked on
its entire localized polynomial base and all THREE presentation generators. -/
theorem field_restriction :
    (originalFieldEmbedding c).comp (infinityMap ℚ c).toRingHom = originalEmbedding c := by
  apply ThreeRootCoordinates318.ringHom_ext
  · apply IsLocalization.ringHom_ext
      (Submonoid.powers (IntegralInfinityChart318.denominator ℚ c))
    apply RingHom.ext
    intro q
    have he : ((originalFieldEmbedding c).comp (infinityMap ℚ c).toRingHom).comp
        (algebraMap ℚ[X] (IntegralInfinityChart318.Order ℚ c)) =
      (originalEmbedding c).comp (algebraMap ℚ[X] (IntegralInfinityChart318.Order ℚ c)) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply,Polynomial.algebraMap_eq,
          ←IsScalarTower.algebraMap_apply,AlgHom.commutes,RingHom.map_rat_algebraMap]
      · change originalFieldEmbedding c (infinityMap ℚ c (IntegralInfinityChart318.coordinate ℚ c)) =
          originalEmbedding c (IntegralInfinityChart318.coordinate ℚ c)
        rw [IntegralRationalInfinityCoordinate318.reciprocal_coordinate,original_coordinate]
    simpa only [RingHom.comp_apply,←IsScalarTower.algebraMap_apply] using RingHom.congr_fun he q
  · intro j
    change originalFieldEmbedding c (infinityMap ℚ c (infinityGenerator ℚ c j)) =
      originalEmbedding c (infinityGenerator ℚ c j)
    rw [generator_original_field]
    change _ = InfinityOpenFractionField318.openEmbedding c
      (rationalOrderEquiv c (infinityGenerator ℚ c j))
    rw [rationalOrderEquiv_generator,InfinityOrderCoordinates318.generator_embedding]

/-- The full infinity restriction commutes with the original rational atlas.
The proof uses all generators and injectivity of the ORIGINAL open embedding. -/
theorem infinity_restriction (a : IntegralInfinityChart318.Order ℚ c) :
    overlapEquiv c (infinityMap ℚ c a) =
      InfinityOverlapLocalization318.toOpen c (rationalOrderEquiv c a) := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  have he := RingHom.congr_fun (field_restriction c) a
  exact he.trans (InfinityOverlapLocalization318.toOpen_embedding c (rationalOrderEquiv c a)).symm
end IntegralRationalInfinityMap318
