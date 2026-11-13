module
public import ActualTwoDescentOriginalRootGenericSquareRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootLocalFieldRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIntegralSchemeRebuild318
open ActualTwoDescentOriginalMarkedStalksRebuild318 ActualTwoDescentOriginalRootLocalParameter318
variable {K : Type*} [Field K] [CharZero K]

/-- Extend the ACTUAL marked-stalk isomorphism to the common original
generic field using its native fraction-ring-of-stalk instance. -/
def comparison (n : K) (i : Fin 3) :
    (originalCubicScheme n).functionField ≃+* FractionRing (RootLocalRing n i) :=
  IsFractionRing.ringEquivOfRingEquiv (rootEquiv n i)

lemma on_stalk (n : K) (i : Fin 3) (s : RootStalk n i) :
    comparison n i
      (algebraMap (RootStalk n i) (originalCubicScheme n).functionField s) =
        algebraMap (RootLocalRing n i) (FractionRing (RootLocalRing n i))
          (rootEquiv n i s) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ s

/-- Named original root function, SAME marked stalk, SAME explicit root
localization. This closes the coefficient normalization, not a Weil map. -/
theorem named_root (n : K) (i : Fin 3) :
    comparison n i (ActualTwoDescentOriginalGenericFunctionsRebuild318.root n
      (ActualTwoDescentOriginalRootIdeals318.root n i)) =
        algebraMap (RootLocalRing n i) (FractionRing (RootLocalRing n i)) (rootLocalF n i) := by
  rw [← ActualTwoDescentOriginalRootGenericSquareRebuild318.root_square, on_stalk]
  simp only [rootF, RingEquiv.apply_symm_apply]
end ActualTwoDescentOriginalRootLocalFieldRebuild318
