module
public import ActualTwoDescentOpenAffineStalkRebuild318
public import ActualTwoDescentInfinityNormalizedOrders318
public section
noncomputable section
namespace ActualTwoDescentOriginalMarkedStalksRebuild318
open AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentOriginalRootMaximalIdeal318 ActualTwoDescentOriginalRootLocalParameter318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentOriginalRootNativeDVR318 ActualTwoDescentInfinityNativeDVR318
variable {K : Type*} [Field K] [CharZero K]

def rootPrime (n : K) (i : Fin 3) : PrimeSpectrum (AffineChart n) :=
  ⟨rootIdeal n i, inferInstance⟩
def infinityPrime (n : K) : PrimeSpectrum (InfinityChart n) :=
  ⟨originIdeal n, inferInstance⟩
def rootPoint (n : K) (i : Fin 3) : originalCubicScheme n :=
  affineChart n (rootPrime n i)
def infinityPoint (n : K) : originalCubicScheme n :=
  infinityChart n (infinityPrime n)
abbrev RootStalk (n : K) (i : Fin 3) :=
  (originalCubicScheme n).presheaf.stalk (rootPoint n i)
abbrev InfinityStalk (n : K) :=
  (originalCubicScheme n).presheaf.stalk (infinityPoint n)

def rootEquiv (n : K) (i : Fin 3) : RootStalk n i ≃+* RootLocalRing n i :=
  ActualTwoDescentOpenAffineStalkRebuild318.equivalence (affineChart n) (rootPrime n i)
def infinityEquiv (n : K) : InfinityStalk n ≃+* InfinityLocalRing n :=
  ActualTwoDescentOpenAffineStalkRebuild318.equivalence (infinityChart n) (infinityPrime n)

instance rootStalkDomain (n : K) (i : Fin 3) : IsDomain (RootStalk n i) :=
  Function.Injective.isDomain (rootEquiv n i) (rootEquiv n i).injective
instance infinityStalkDomain (n : K) : IsDomain (InfinityStalk n) :=
  Function.Injective.isDomain (infinityEquiv n) (infinityEquiv n).injective
instance rootStalkDVR (n : K) (i : Fin 3) [Fact (n ≠ 0)] :
    IsDiscreteValuationRing (RootStalk n i) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (rootEquiv n i).symm
instance infinityStalkDVR (n : K) : IsDiscreteValuationRing (InfinityStalk n) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (infinityEquiv n).symm

def rootY (n : K) (i : Fin 3) : RootStalk n i :=
  (rootEquiv n i).symm (rootLocalY n i)
def rootF (n : K) (i : Fin 3) : RootStalk n i :=
  (rootEquiv n i).symm (rootLocalF n i)
def infinityU (n : K) : InfinityStalk n := (infinityEquiv n).symm (localU n)
def infinityV (n : K) : InfinityStalk n := (infinityEquiv n).symm (localV n)

lemma rootY_is_actual_coordinate (n : K) (i : Fin 3) :
    rootY n i = ActualTwoDescentOpenAffineStalkRebuild318.coefficient
      (affineChart n) (rootPrime n i) (affineY n) := rfl
lemma rootF_is_actual_coordinate (n : K) (i : Fin 3) :
    rootF n i = ActualTwoDescentOpenAffineStalkRebuild318.coefficient
      (affineChart n) (rootPrime n i) (rootNumerator n i) := rfl
lemma infinityU_is_actual_coordinate (n : K) :
    infinityU n = ActualTwoDescentOpenAffineStalkRebuild318.coefficient
      (infinityChart n) (infinityPrime n) (chartU n) := rfl
lemma infinityV_is_actual_coordinate (n : K) :
    infinityV n = ActualTwoDescentOpenAffineStalkRebuild318.coefficient
      (infinityChart n) (infinityPrime n) (chartV n) := rfl
end ActualTwoDescentOriginalMarkedStalksRebuild318
