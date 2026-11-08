module
public import InfinityReciprocalAction318
public import ThreeRootCoordinates318
public section
noncomputable section
namespace InfinityOrderCoordinates318
open Polynomial
open scoped TensorProduct
open InfinityReciprocalAction318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
local instance originalField:Field (L c):=(KummerTensorField318.source_raw_field c).toField
@[expose] def coefficient (j:Fin 3):InfinityOpenChart318.OpenBase c:=
  algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c) (InfinityParameters318.coefficient c j)
@[expose] def generator (j:Fin 3):Order c:=ThreeRootCoordinates318.generator (coefficient c) j
@[expose] def coordinate:Order c:=
  algebraMap (InfinityOpenChart318.OpenBase c) (Order c)
    (algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c) X)

theorem coordinate_embedding:InfinityOpenFractionField318.openEmbedding c (coordinate c)=
    InfinityFieldCoordinates318.u c:=by
  rw [coordinate,ReciprocalInfinityNormalization318.openEmbedding_on_polynomial,Polynomial.aeval_X]

lemma unlocalized_generator (j:Fin 3):
    InfinityOpenChart318.embedding c
      (ThreeRootCoordinates318.generator (InfinityParameters318.coefficient c) j)=
    InfinityFieldEquivalence318.generator c j:=by
  exact ThreeRootCoordinates318.coefficientMap_generator _ (RatFunc ℚ) j

lemma original_generator (j:Fin 3):
    InfinityFractionField318.originalEmbedding c
      (ThreeRootCoordinates318.generator (InfinityParameters318.coefficient c) j)=
      InfinityFieldCoordinates318.ratio c j:=by
  change InfinityFieldEquivalence318.fieldEquiv c (InfinityOpenChart318.embedding c _)=_
  rw [unlocalized_generator,InfinityFieldEquivalence318.fieldEquiv_on_generator]

lemma orderToOpen_generator (j:Fin 3):
    InfinityOpenFractionField318.orderToOpen c
      (ThreeRootCoordinates318.generator (InfinityParameters318.coefficient c) j)=generator c j:=
  ThreeRootCoordinates318.coefficientMap_generator _ (InfinityOpenChart318.OpenBase c) j

/-- The actual presentation generators equal the original full-field root ratios. -/
theorem generator_embedding (j:Fin 3):InfinityOpenFractionField318.openEmbedding c (generator c j)=
    InfinityFieldCoordinates318.ratio c j:=by
  rw [←orderToOpen_generator,InfinityOpenFractionField318.openEmbedding_on_order,original_generator]

theorem generator_eq_ratio (j:Fin 3):generator c j=InfinityCharacterUnits318.ratio c j:=
  InfinityOpenFractionField318.openEmbedding_injective c
    ((generator_embedding c j).trans (InfinityCharacterUnits318.ratio_embedding c j).symm)
theorem generator_unit (j:Fin 3):IsUnit (generator c j):=by
  rw [generator_eq_ratio]
  exact InfinityCharacterUnits318.ratio_unit c j
end InfinityOrderCoordinates318
