module
public import OriginalAllPlaceNormalModel318
public import IntegralNormalModelFlat318
public section
noncomputable section
namespace OriginalNormalModelFlatFamily318
open NumberField CategoryTheory AlgebraicGeometry
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318
set_option maxHeartbeats 1000000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : Data c t w) (M : Realization c t w D)

/-- The actual original integral center makes the same structure map
surjective over the entire valuation ring, not just on the generic point. -/
theorem surjective : Surjective M.structureMap := by
  constructor
  intro x
  refine ⟨M.center x,?_⟩
  change (M.center ≫ M.structureMap) x = x
  have h : M.center ≫ M.structureMap = 𝟙 _ := M.center_base
  rw [h]
  rfl

theorem flat : Flat M.structureMap := by
  letI : IsIntegral M.scheme := M.integral
  letI := surjective c t w D M
  letI : IsDominant M.structureMap := inferInstance
  exact IntegralNormalModelFlat318.integral_dominant_flat M.scheme M.structureMap

theorem proper_flat_finitelyPresented : IsProper M.structureMap ∧ Flat M.structureMap ∧
    Surjective M.structureMap ∧ LocallyOfFinitePresentation M.structureMap := by
  letI := M.proper
  exact ⟨inferInstance,flat c t w D M,surjective c t w D M,inferInstance⟩

/-- Original-input-only proper flat normal arithmetic family, with its
same exact full-source generic specialization and signed root recovery
stored in Realization. No claim about smooth special fibers is added. -/
theorem exists_original_flat_family
    (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0) :
    ∃ (D : Data c t w) (M : Realization c t w D),
      IsProper M.structureMap ∧ Flat M.structureMap ∧ Surjective M.structureMap ∧
      LocallyOfFinitePresentation M.structureMap := by
  obtain ⟨D,⟨M⟩⟩ := exists_original_realization c t w hn
  exact ⟨D,M,proper_flat_finitelyPresented c t w D M⟩
end OriginalNormalModelFlatFamily318
