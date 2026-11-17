module
public import ActualTwoDescentLocalizationFractionEquivalence318
public section
noncomputable section
namespace ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeDomain318
open ActualTwoDescentInfinityNativeFractionFunctions318 ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentOriginalOverlapEquivalence318 ActualTwoDescentOriginalOverlapInjectivity318
open ActualTwoDescentLocalizationFractionEquivalence318 ActualTwoDescentOriginalFunctionFieldTheta318
variable {K : Type*} [Field K] [CharZero K]

instance affinePunctureDomain (n : K) : IsDomain (AffinePuncture n) :=
  IsLocalization.Away.isDomain _ (actual_affine_y_nonzero n)
instance infinityPunctureDomain (n : K) : IsDomain (InfinityPuncture n) :=
  IsLocalization.Away.isDomain _ (actual_chart_v_nonzero n)

def affineFractionOpenEquiv (n : K) : OriginalFunctionField n ≃+* FractionRing (AffinePuncture n) :=
  localizationFractionEquiv (AffineChart n) (AffinePuncture n) (Submonoid.powers (affineY n))
    (actual_affine_open_injective n)
def puncturedFractionEquiv (n : K) : FractionRing (AffinePuncture n) ≃+* FractionRing (InfinityPuncture n) :=
  IsFractionRing.ringEquivOfRingEquiv (originalOverlapEquiv n)
def infinityFractionOpenEquiv (n : K) : FractionRing (InfinityChart n) ≃+* FractionRing (InfinityPuncture n) :=
  localizationFractionEquiv (InfinityChart n) (InfinityPuncture n) (Submonoid.powers (chartV n))
    (actual_infinity_open_injective n)
def infinityFractionLocalEquiv (n : K) : FractionRing (InfinityChart n) ≃+* InfinityFractionField n :=
  localizationFractionEquiv (InfinityChart n) (InfinityLocalRing n) (originIdeal n).primeCompl
    (actual_local_map_injective n)

/-- The EARLIER original affine FunctionField is now explicitly
identified with the fraction field of the ACTUAL original infinity DVR.
Every intermediate ring/map is the literal original chart localization. -/
def originalNativeFunctionFieldEquiv (n : K) : OriginalFunctionField n ≃+* InfinityFractionField n :=
  (affineFractionOpenEquiv n).trans ((puncturedFractionEquiv n).trans
    ((infinityFractionOpenEquiv n).symm.trans (infinityFractionLocalEquiv n)))
end ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
