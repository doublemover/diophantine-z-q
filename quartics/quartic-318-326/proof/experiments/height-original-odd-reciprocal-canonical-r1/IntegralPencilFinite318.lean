module
public import IntegralPencilPreimages318
public section
noncomputable section
namespace IntegralPencilFinite318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralPencilScalarMaps318 IntegralWholeReciprocalGluing318
open IntegralWholePencilMap318 IntegralPencilPreimages318
open IntegralPencilChartFiniteness318
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_square : IsPullback
    (Spec.map (CommRingCat.ofHom (finiteCoordinate R c).toRingHom))
    (finiteChart R c) (JLineAtlas318.chart R 1) (projection R c) := by
  apply IsOpenImmersion.isPullback
  · exact finite_restriction R c
  · exact finite_preimage R c

theorem reciprocal_square : IsPullback
    (Spec.map (CommRingCat.ofHom (reciprocalCoordinate R c).toRingHom))
    (infinityChart R c) (JLineAtlas318.chart R 0) (projection R c) := by
  apply IsOpenImmersion.isPullback
  · exact reciprocal_restriction R c
  · exact reciprocal_preimage R c

/-- A reducible concrete presentation of the original two-chart target
cover, retaining the original JLineAtlas maps and its proved coverage. -/
abbrev targetCover : (ProjectiveJLine318.scheme R).OpenCover where
  I₀ := Fin 2
  X _ := Spec (CommRingCat.of (Polynomial R))
  f := JLineAtlas318.chart R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,inferInstance⟩
    intro p
    have hp : p ∈ (⊤ : (ProjectiveJLine318.scheme R).Opens) := trivial
    rw [←JLineAtlas318.standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at hp
    obtain ⟨j,hj⟩ := hp
    rw [←JLineAtlas318.chart_range] at hj
    obtain ⟨q,hq⟩ := hj
    exact ⟨j,q,hq⟩

/-- The full gluing has a genuine FINITE projection to the actual projective
line. Both affine orders are the entire target-chart pullbacks, so local
finiteness applies to the correct maps rather than just smaller opens. -/
instance projection_finite : IsFinite (projection R c) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P:=@IsFinite) (targetCover R)]
  intro i
  fin_cases i
  · change IsFinite (pullback.snd (projection R c) (JLineAtlas318.chart R 0))
    rw [←(reciprocal_square R c).flip.isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (projection R c) (JLineAtlas318.chart R 1))
    rw [←(finite_square R c).flip.isoPullback_inv_snd]
    infer_instance

/-- Finiteness of the actual original contact pencil on the original model,
using its explicit scheme comparison, not just the auxiliary y0 map. -/
instance original_finite : IsFinite (IntegralOriginalContactPencil318.projection R c) := by
  unfold IntegralOriginalContactPencil318.projection
  infer_instance

/-- The morphism constructed from the original generating J² pair is finite. -/
theorem section_pencil_finite
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsFinite (IntegralSectionProjectiveMap318.projectiveMap R c hN) := by
  rw [IntegralSectionProjectiveMap318.projectiveMap_eq]
  infer_instance
end IntegralPencilFinite318
