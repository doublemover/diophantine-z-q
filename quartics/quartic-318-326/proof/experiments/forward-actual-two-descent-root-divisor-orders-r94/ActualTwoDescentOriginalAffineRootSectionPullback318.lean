module
public import ActualTwoDescentOriginalAffineOverlapInclusion318
public section
noncomputable section
namespace ActualTwoDescentOriginalAffineRootSectionPullback318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapPoleIdentity318
open ActualTwoDescentOriginalRootOverlapRefinement318 ActualTwoDescentOriginalOverlapSquareSections318
universe u
variable {K : Type u} [Field K] [CharZero K]

def principalRootSection (n : K) (i : Fin 3) (b : Bool) :
    Γ(Spec (CommRingCat.of (RootChartRing n i b)),⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (RootChartRing n i b))).inv (rootChartMap n i b (rootNumerator n i))

/-- The old affine root function pulls back to the SAME original
common-chart section,by its literal localization lift,not a field equality. -/
lemma actual_principal_root_pullback (n : K) (i : Fin 3) (b : Bool) :
    (intoRootChart n i b).appTop (principalRootSection n i b)=rootSection n i := by
  have hh := (congrArg (fun f => f (rootChartMap n i b (rootNumerator n i)))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (rootOverlapMap n i b)))).symm
  change (intoRootChart n i b).appTop (principalRootSection n i b)=
    (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv
      (rootOverlapMap n i b (rootChartMap n i b (rootNumerator n i))) at hh
  rw [actual_root_overlap_base] at hh
  rw [rootSection_value]
  exact hh
end ActualTwoDescentOriginalAffineRootSectionPullback318
