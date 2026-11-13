module
public import ActualTwoDescentOriginalRootFractionalSheafRebuild318
public import IdentityCotangent318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinityLocalPullbackRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealInfinityFrame318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentInfinityChartRing318
universe u
variable {K : Type u} [Field K] [CharZero K]

def localMap (n : K) : Spec (CommRingCat.of (InfinityLocalRing n)) ⟶ infinityScheme n :=
  Spec.map (CommRingCat.ofHom (algebraMap (InfinityChart n) (InfinityLocalRing n)))
def map (n : K) := localMap n ≫ infinityChart n

/-- Pull the exact old infinity projection frame to the actual origin
local spectrum; do not replace it with a chosen trivialization. -/
def frame (n : K) (i : Fin 3) :
    (Scheme.Modules.pullback (map n)).obj (originalRootIdealSheaf n i) ≅
    SheafOfModules.unit (Spec (CommRingCat.of (InfinityLocalRing n))).ringCatSheaf :=
  ((Scheme.Modules.pullbackComp (localMap n) (infinityChart n)).app
      (originalRootIdealSheaf n i)).symm ≪≫
  (Scheme.Modules.pullback (localMap n)).mapIso
    (((Scheme.Modules.restrictFunctorIsoPullback (infinityChart n)).app
      (originalRootIdealSheaf n i)).symm ≪≫ originalInfinityFrame n i) ≪≫
  IdentityCotangent318.pullbackUnitIso (localMap n)
end ActualTwoDescentOriginalInfinityLocalPullbackRebuild318
