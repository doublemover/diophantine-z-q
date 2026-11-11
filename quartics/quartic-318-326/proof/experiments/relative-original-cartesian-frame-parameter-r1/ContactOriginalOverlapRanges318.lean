module
public import ContactOriginalRelativeOverlap318
public section
noncomputable section
namespace ContactOriginalOverlapRanges318
open AlgebraicGeometry CategoryTheory
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeOverlap318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

lemma original_intersection : (into R c).opensRange =
    (finiteInto R c).opensRange ⊓ (infinityInto R c).opensRange := by
  rw [full_intersection,finite_range,infinity_range]

lemma infinity_edge_range : (infinityEdge R c).opensRange =
    (infinityInto R c) ⁻¹ᵁ (finiteInto R c).opensRange := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change infinityInto R c (infinityEdge R c y) ∈ (finiteInto R c).opensRange
    have h := congrArg (fun k => k y) (infinityEdge_into R c)
    rw [← Scheme.Hom.comp_apply,h]
    have hy : into R c y ∈ (into R c).opensRange := ⟨y,rfl⟩
    rw [original_intersection] at hy
    exact hy.1
  · intro hx
    have hy : infinityInto R c x ∈ (into R c).opensRange := by
      rw [original_intersection]
      exact ⟨hx,⟨x,rfl⟩⟩
    obtain ⟨y,hy⟩ := hy
    refine ⟨y,?_⟩
    apply (infinityInto R c).isOpenEmbedding.injective
    change (infinityEdge R c ≫ infinityInto R c) y = _
    rw [infinityEdge_into]
    exact hy

lemma finite_edge_range : (finiteEdge R c).opensRange =
    (finiteInto R c) ⁻¹ᵁ (infinityInto R c).opensRange := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change finiteInto R c (finiteEdge R c y) ∈ (infinityInto R c).opensRange
    have h := congrArg (fun k => k y) (finiteEdge_into R c)
    rw [← Scheme.Hom.comp_apply,h]
    have hy : into R c y ∈ (into R c).opensRange := ⟨y,rfl⟩
    rw [original_intersection] at hy
    exact hy.2
  · intro hx
    have hy : finiteInto R c x ∈ (into R c).opensRange := by
      rw [original_intersection]
      exact ⟨⟨x,rfl⟩,hx⟩
    obtain ⟨y,hy⟩ := hy
    refine ⟨y,?_⟩
    apply (finiteInto R c).isOpenEmbedding.injective
    change (finiteEdge R c ≫ finiteInto R c) y = _
    rw [finiteEdge_into]
    exact hy
end ContactOriginalOverlapRanges318
