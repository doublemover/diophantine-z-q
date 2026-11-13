module
public import ActualTwoDescentOriginalAffineAtPrimePullbackRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalLocalFieldEmbeddingsRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentOriginalRootLocalParameter318
open ActualTwoDescentInfinityLocalParameter318
variable {K : Type*} [Field K] [CharZero K]

/-- Both local coefficient embeddings factor through the ACTUAL
original marked stalk and its canonical generic specialization. -/
def rootEmbedding (n : K) (i : Fin 3) : RootLocalRing n i →+* (originalCubicScheme n).functionField :=
  (algebraMap (RootStalk n i) (originalCubicScheme n).functionField).comp (rootEquiv n i).symm.toRingHom

def infinityEmbedding (n : K) : InfinityLocalRing n →+* (originalCubicScheme n).functionField :=
  (algebraMap (InfinityStalk n) (originalCubicScheme n).functionField).comp (infinityEquiv n).symm.toRingHom

lemma root_injective (n : K) (i : Fin 3) : Function.Injective (rootEmbedding n i) :=
  (IsFractionRing.injective _ _).comp (rootEquiv n i).symm.injective
lemma infinity_injective (n : K) : Function.Injective (infinityEmbedding n) :=
  (IsFractionRing.injective _ _).comp (infinityEquiv n).symm.injective

lemma root_named (n : K) (i : Fin 3) : rootEmbedding n i (rootLocalF n i)=
    ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
      (ActualTwoDescentOriginalRootIdeals318.root n i) :=
  ActualTwoDescentOriginalRootGenericSquareRebuild318.root_square n i

lemma infinity_parameter (n : K) : infinityEmbedding n (localU n)=
    algebraMap (InfinityStalk n) (originalCubicScheme n).functionField (infinityU n) := rfl
lemma infinity_parameter_nonzero (n : K) : infinityEmbedding n (localU n) ≠ 0 := by
  rw [infinity_parameter]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
    (ActualTwoDescentOriginalStalkFactorsRebuild318.infinity_uniformizer n).ne_zero
end ActualTwoDescentOriginalLocalFieldEmbeddingsRebuild318
