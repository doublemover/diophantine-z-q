module
public import ActualTwoDescentOriginalIdealInfinityFrame318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealEverywhereFramed318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalGlobalRootAffineFrames318 ActualTwoDescentOriginalIdealInfinityFrame318
open ActualTwoDescentOriginalRootRefinedCover318 ActualTwoDescentRootPrincipalOpenCover318
open ActualTwoDescentOriginalRootIdealRestrictionComparison318
variable {K : Type*} [Field K] [CharZero K]

/-- At EVERY scheme point the actual global root-ideal module has a
frame on an actual open neighbourhood. n≠0 is used exactly for coverage. -/
theorem actual_original_ideal_everywhere_framed (n : K) (hn : n≠0) (i : Fin 3)
    (p : originalCubicScheme n) :
    ∃ (Y : Scheme) (j : Y ⟶ originalCubicScheme n) (_ : IsOpenImmersion j) (q : Y),
      j q=p ∧ Nonempty ((originalRootIdealSheaf n i).restrict j ≅
        SheafOfModules.unit Y.ringCatSheaf) := by
  rcases actual_original_root_refinement_covers n hn i p with ⟨b,q,hq⟩|⟨q,hq⟩
  · refine ⟨Spec (CommRingCat.of (RootChartRing n i b)),
      rootLocalizationMorphism n i b ≫ affineChart n,inferInstance,q,?_,
      ⟨originalGlobalAffineFrame n i b⟩⟩
    exact hq
  · exact ⟨infinityScheme n,infinityChart n,inferInstance,q,hq,⟨originalInfinityFrame n i⟩⟩
end ActualTwoDescentOriginalIdealEverywhereFramed318
