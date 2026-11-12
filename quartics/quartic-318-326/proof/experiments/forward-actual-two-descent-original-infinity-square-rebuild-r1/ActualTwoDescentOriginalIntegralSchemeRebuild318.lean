module
public import ActualTwoDescentOriginalStalkOrdersRebuild318
public import ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.Sets.OpenCover
public section
noncomputable section
namespace ActualTwoDescentOriginalIntegralSchemeRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalCubicChartCover318
open ActualTwoDescentOriginalNativeFunctionFieldEquivalence318
variable {K : Type*} [Field K] [CharZero K]

/-- The surviving geometry two-chart cover construction, instantiated on
the ORIGINAL cubic and its actual localization overlap. -/
def cover (n : K) : (originalCubicScheme n).OpenCover where
  I₀ := Bool
  X k := if k then affineScheme n else infinityScheme n
  f k := by cases k; exact infinityChart n; exact affineChart n
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      rcases actual_original_charts_cover n p with ⟨q,hq⟩ | ⟨q,hq⟩
      · exact ⟨true,q,hq⟩
      · exact ⟨false,q,hq⟩
    · intro k; cases k <;> infer_instance

lemma intersection_nonempty (n : K) :
    ((affineChart n).opensRange ⊓ (infinityChart n).opensRange :
      (originalCubicScheme n).Opens) ≠ ⊥ := by
  obtain ⟨p⟩ : Nonempty (overlapScheme n) := inferInstance
  intro h
  have hp : affineChart n (intoAffine n p) ∈
      ((affineChart n).opensRange ⊓ (infinityChart n).opensRange) := by
    refine ⟨⟨_,rfl⟩,⟨intoInfinity n p,?_⟩⟩
    change (intoInfinity n ≫ infinityChart n) p = (intoAffine n ≫ affineChart n) p
    exact congrArg (fun f : overlapScheme n ⟶ originalCubicScheme n => f p)
      (pushout.condition (f := intoAffine n) (g := intoInfinity n)).symm
  rw [h] at hp
  exact hp

theorem irreducible (n : K) : IrreducibleSpace (originalCubicScheme n) := by
  let U : Bool → (originalCubicScheme n).Opens := fun k =>
    if k then (affineChart n).opensRange else (infinityChart n).opensRange
  have hi : ∀ k : Bool, IsPreirreducible (U k : Set (originalCubicScheme n)) := by
    intro k
    cases k
    · simpa [U,Set.image_univ] using
        (PreirreducibleSpace.isPreirreducible_univ (X := infinityScheme n)).image
          (infinityChart n) (infinityChart n).continuous.continuousOn
    · simpa [U,Set.image_univ] using
        (PreirreducibleSpace.isPreirreducible_univ (X := affineScheme n)).image
          (affineChart n) (affineChart n).continuous.continuousOn
  have hn : Pairwise (fun i j => ¬Disjoint (U i) (U j)) := by
    intro i j hij
    cases i <;> cases j <;> simp only [ne_eq,not_true_eq_false] at hij
    · simpa [U,disjoint_iff,inf_comm] using intersection_nonempty n
    · simpa [U,disjoint_iff] using intersection_nonempty n
  have hu : (Set.univ : Set (originalCubicScheme n)) ⊆
      ⋃ k : Bool, (U k : Set (originalCubicScheme n)) := by
    intro p _
    rcases actual_original_charts_cover n p with ⟨q,hq⟩ | ⟨q,hq⟩
    · exact mem_iUnion.mpr ⟨true,q,hq⟩
    · exact mem_iUnion.mpr ⟨false,q,hq⟩
  rw [irreducibleSpace_def]
  exact ⟨⟨affineChart n (Classical.choice inferInstance),mem_univ _⟩,
    IsPreirreducible.of_subset_iUnion hn hi isOpen_univ hu⟩

theorem reduced (n : K) : IsReduced (originalCubicScheme n) := by
  haveI : ∀ k, IsReduced ((cover n).X k) := by
    intro k
    cases k <;> change IsReduced (Spec (CommRingCat.of _)) <;> infer_instance
  exact IsReduced.of_openCover _ (cover n)

/-- No nonsingularity or n≠0 is used to produce integrality. -/
instance integral (n : K) : IsIntegral (originalCubicScheme n) := by
  letI := irreducible n
  letI := reduced n
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end ActualTwoDescentOriginalIntegralSchemeRebuild318
