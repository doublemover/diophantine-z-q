module
public import IntegralPencilChartFlat318
public section
noncomputable section
namespace IntegralOriginalFiniteFlatPencil318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralPencilFinite318 IntegralWholePencilMap318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- Flatness is checked on the same ENTIRE target-chart pullbacks used for
finiteness. Ramification is retained; étaleness of the contact pencil is
neither required nor inferred. -/
instance whole_flat : Flat (projection R c) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P:=@Flat) (targetCover R)]
  intro i
  fin_cases i
  · change Flat (pullback.snd (projection R c) (JLineAtlas318.chart R 0))
    rw [←(reciprocal_square R c).flip.isoPullback_inv_snd]
    infer_instance
  · change Flat (pullback.snd (projection R c) (JLineAtlas318.chart R 1))
    rw [←(finite_square R c).flip.isoPullback_inv_snd]
    infer_instance

instance original_flat : Flat (IntegralOriginalContactPencil318.projection R c) := by
  unfold IntegralOriginalContactPencil318.projection
  infer_instance

/-- The exact original section-defined pencil is finite and flat. The
rank16 assertion remains attached to its actual whole finite t-chart. -/
theorem section_pencil_finite_flat
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsFinite (IntegralSectionProjectiveMap318.projectiveMap R c hN) ∧
    Flat (IntegralSectionProjectiveMap318.projectiveMap R c hN) := by
  rw [IntegralSectionProjectiveMap318.projectiveMap_eq]
  exact ⟨inferInstance,inferInstance⟩
end IntegralOriginalFiniteFlatPencil318
