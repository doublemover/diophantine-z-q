module
public import ActualTwoDescentOriginalRootFractionalModuleRebuild318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootFractionalSheafRebuild318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalDegreeZeroIdealSheaf318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentOriginalRootLocalParameter318 ActualTwoDescentOriginalRootFractionalModuleRebuild318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Native pullback of the EXISTING global ideal sheaf to the literal
root local spectrum, identified with the exact fractional yR module. -/
def iso (n : K) (hn : n ≠ 0) (i : Fin 3) :
    (Scheme.Modules.pullback
      (ActualTwoDescentOriginalAffineAtPrimePullbackRebuild318.map n (rootIdeal n i))).obj
      (originalRootIdealSheaf n i) ≅
    tilde (R:=CommRingCat.of (RootLocalRing n i)) (ModuleCat.of (RootLocalRing n i) (lattice n i)) :=
  ActualTwoDescentOriginalAffineAtPrimePullbackRebuild318.iso n i (rootIdeal n i) ≪≫
    (tilde.functor (CommRingCat.of (RootLocalRing n i))).mapIso (equivalence n hn i).toModuleIso

lemma hom_formula (n : K) (hn : n ≠ 0) (i : Fin 3) : (iso n hn i).hom=
    (ActualTwoDescentOriginalAffineAtPrimePullbackRebuild318.iso n i (rootIdeal n i)).hom ≫
    (tilde.functor (CommRingCat.of (RootLocalRing n i))).map (equivalence n hn i).toModuleIso.hom := rfl
end ActualTwoDescentOriginalRootFractionalSheafRebuild318
