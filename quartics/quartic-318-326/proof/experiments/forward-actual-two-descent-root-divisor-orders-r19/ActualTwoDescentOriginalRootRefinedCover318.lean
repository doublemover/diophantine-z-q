module
public import ActualTwoDescentRootLocalTensorSquare318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootRefinedCover318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentRootPrincipalOpenCover318
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalCubicChartCover318
variable {K : Type*} [Field K] [CharZero K]

/-- The actual principal-open inclusions into the SAME original cubic
scheme; no replacement abstract curve enters the module construction. -/
def refinedAffineChart (n : K) (hn : n≠0) (i : Fin 3) (b : Bool) :
    Spec (CommRingCat.of (RootChartRing n i b)) ⟶ originalCubicScheme n :=
  (rootAffineCover n hn i).f b ≫ affineChart n
instance refinedAffineChart_open (n : K) (hn : n≠0) (i : Fin 3) (b : Bool) :
    IsOpenImmersion (refinedAffineChart n hn i b) := by
  unfold refinedAffineChart
  infer_instance

/-- Genuine three-chart coverage, including non-rational scheme points
and the root-containing affine chart. This is the exact domain on which
the constructed root-ideal frames and the global infinity data meet. -/
theorem actual_original_root_refinement_covers (n : K) (hn : n≠0) (i : Fin 3)
    (p : originalCubicScheme n) :
    (∃ (b : Bool) (q : Spec (CommRingCat.of (RootChartRing n i b))),
      refinedAffineChart n hn i b q=p) ∨ (∃ q,infinityChart n q=p) := by
  rcases actual_original_charts_cover n p with ⟨a,ha⟩|h∞
  · left
    obtain ⟨q,hq⟩ := (rootAffineCover n hn i).covers a
    refine ⟨(rootAffineCover n hn i).idx a,q,?_⟩
    change affineChart n ((rootAffineCover n hn i).f ((rootAffineCover n hn i).idx a) q)=p
    rw [hq,ha]
  · exact Or.inr h∞

/-- Every refined affine inclusion preserves the original structural
map, with no unit rescaling or unproved model identification. -/
lemma actual_refined_chart_structure (n : K) (hn : n≠0) (i : Fin 3) (b : Bool) :
    refinedAffineChart n hn i b ≫ structureMap n=
      (rootAffineCover n hn i).f b ≫ affineStructure n := by
  rw [refinedAffineChart,Category.assoc,actual_affine_chart_structure]
end ActualTwoDescentOriginalRootRefinedCover318
