module
public import UniversalScalarCoordinate318
public section
noncomputable section
namespace UniversalCoordinateGeneration318
open scoped TensorProduct
universe u v w
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
  (B : Type w) [CommRing B] [Algebra R B] (ell : P →ₗ[R] B)

/-- Actual generation of the coordinate ring produces the primitive
section internally; the consumer no longer asks for a value-one vector. -/
theorem exists_primitive
    (h : Submodule.span B (Set.range ell) = ⊤) :
    ∃ s : B ⊗[R] P, ell.liftBaseChange B s=1 := by
  have hs : Submodule.span B (Set.range ell) ≤ (ell.liftBaseChange B).range := by
    apply Submodule.span_le.mpr
    rintro y ⟨p,rfl⟩
    exact ⟨1 ⊗ₜ[R] p,by rw [LinearMap.liftBaseChange_one_tmul]⟩
  rw [h] at hs
  exact hs (Submodule.mem_top : (1 : B) ∈ (⊤ : Submodule B B))

/-- The SAME evaluated universal coefficient is regular under a genuine
coordinate-generation statement. Flatness of specialization is NOT
asserted: the zero parameter still specializes the section to zero. -/
theorem regular (h : Submodule.span B (Set.range ell) = ⊤)
    (a : B ⊗[R] ProjectiveSectionParameter318.algebra R P)
    (ha : a * UniversalScalarCoordinate318.coefficient R P B ell=0) : a=0 := by
  obtain ⟨s,hs⟩ := exists_primitive R P B ell h
  exact UniversalScalarCoordinate318.regular R P B ell s hs a ha
end UniversalCoordinateGeneration318
