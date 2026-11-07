module
public import InfinityCoordinateDomain318
public import WeierstrassBaseChange318
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Sets.OpenCover
import all WeierstrassGluing318
import all WeierstrassBaseChange318
public section
noncomputable section
namespace CompletedIntegral318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] [IsDomain R]

lemma chart_intersection (A B:R) :
    ((WeierstrassGluing318.finiteChart A B).opensRange ⊓
      (WeierstrassGluing318.infinityChart A B).opensRange :
      (WeierstrassGluing318.scheme A B).Opens) ≠ ⊥ := by
  have := InfinityCoordinateDomain318.infinity_overlap_domain A B
  obtain ⟨p⟩ := (inferInstance : Nonempty (WeierstrassGluing318.overlap A B))
  intro h
  have hp : WeierstrassGluing318.finiteChart A B (WeierstrassGluing318.intoAffine A B p) ∈
      ((WeierstrassGluing318.finiteChart A B).opensRange ⊓
      (WeierstrassGluing318.infinityChart A B).opensRange) := by
    refine ⟨⟨_,rfl⟩,⟨WeierstrassGluing318.intoInfinity A B p,?_⟩⟩
    change (WeierstrassGluing318.intoInfinity A B ≫ WeierstrassGluing318.infinityChart A B) p =
      (WeierstrassGluing318.intoAffine A B ≫ WeierstrassGluing318.finiteChart A B) p
    rw [WeierstrassGluing318.infinityChart,WeierstrassGluing318.finiteChart,pushout.condition]
  rw [h] at hp
  exact hp

/-- The actual two-chart completion is irreducible over every domain. -/
theorem completed_irreducible (A B:R) : IrreducibleSpace (WeierstrassGluing318.scheme A B) := by
  have := AffineCoordinateDomain318.affine_domain A B
  have := InfinityCoordinateDomain318.infinity_domain A B
  have : IsIntegral (ShortAffineScheme318.scheme A B) := by
    change IsIntegral (Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B)))
    infer_instance
  let U : Bool → (WeierstrassGluing318.scheme A B).Opens := fun b =>
    if b then (WeierstrassGluing318.finiteChart A B).opensRange
    else (WeierstrassGluing318.infinityChart A B).opensRange
  have hi : ∀ b : Bool, IsPreirreducible (U b : Set (WeierstrassGluing318.scheme A B)) := by
    intro b
    cases b
    · simpa [U,Set.image_univ] using (PreirreducibleSpace.isPreirreducible_univ (X:=InfinitySmooth318.scheme A B)).image
        (WeierstrassGluing318.infinityChart A B) (WeierstrassGluing318.infinityChart A B).continuous.continuousOn
    · simpa [U,Set.image_univ] using (PreirreducibleSpace.isPreirreducible_univ (X:=ShortAffineScheme318.scheme A B)).image
        (WeierstrassGluing318.finiteChart A B) (WeierstrassGluing318.finiteChart A B).continuous.continuousOn
  have hn : Pairwise (fun i j => ¬ Disjoint (U i) (U j)) := by
    intro i j hij
    cases i <;> cases j <;> simp only [ne_eq,not_true_eq_false] at hij
    · simpa [U,disjoint_iff,inf_comm] using chart_intersection A B
    · simpa [U,disjoint_iff] using chart_intersection A B
  have hu : (Set.univ : Set (WeierstrassGluing318.scheme A B)) ⊆ ⋃ b : Bool, (U b : Set (WeierstrassGluing318.scheme A B)) := by
    intro p _
    rcases WeierstrassGluing318.charts_cover A B p with ⟨q,hq⟩ | ⟨q,hq⟩
    · exact mem_iUnion.mpr ⟨true,q,hq⟩
    · exact mem_iUnion.mpr ⟨false,q,hq⟩
  rw [irreducibleSpace_def]
  exact ⟨⟨WeierstrassGluing318.finiteChart A B (Classical.choice inferInstance),mem_univ _⟩,
    IsPreirreducible.of_subset_iUnion hn hi isOpen_univ hu⟩

/-- Reducedness is checked on the actual affine open cover. -/
theorem completed_reduced (A B:R) : IsReduced (WeierstrassGluing318.scheme A B) := by
  have := AffineCoordinateDomain318.affine_domain A B
  have := InfinityCoordinateDomain318.infinity_domain A B
  let cover := WeierstrassBaseChange318.twoChartCover A B
  have : ∀ i, IsReduced (cover.X i) := by
    intro i
    cases i <;> change IsReduced (Spec (CommRingCat.of _)) <;> infer_instance
  exact IsReduced.of_openCover _ cover

/-- Genuine integrality of the constructed completion, not a supplied fiber property. -/
theorem completed_integral (A B:R) : IsIntegral (WeierstrassGluing318.scheme A B) := by
  have := completed_irreducible A B
  have := completed_reduced A B
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end CompletedIntegral318
