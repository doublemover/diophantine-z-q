module
public import ThreeRootBaseGeneratorTransport318
public section
noncomputable section
namespace IntegralWholeGeneratorComparisons318
open Polynomial ThreeRootCoordinates318
open IntegralWholeReciprocalOrders318 IntegralWholeFiniteComparison318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- Every full finite-order generator is the corresponding original
root-coordinate-order generator, with no sign or indexing ambiguity. -/
theorem finite_generator (j : Fin 3) :
    coordinateComparison R c (generator (rootCoefficient R c) j)=
      generator (finiteCoefficient R c) j :=
  ThreeRootBaseGeneratorTransport318.three_generator _ _ _ _ j

/-- Passing from the whole reciprocal order to the existing infinity chart
preserves each actual ratio root, not just its square. -/
theorem infinity_generator (j : Fin 3) :
    IntegralOriginalInfinityEmbedding318.ringMap R c
      (generator (IntegralInfinityChart318.coefficient R c) j)=
        IntegralOverlapRootGenerators318.infinityGenerator R c j :=
  coefficientMap_generator _ (IntegralInfinityChart318.Base R c) j
end IntegralWholeGeneratorComparisons318
