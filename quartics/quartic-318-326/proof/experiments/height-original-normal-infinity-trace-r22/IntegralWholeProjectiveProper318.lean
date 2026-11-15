module
public import IntegralWholeProjectivePreimages318
public section
noncomputable section
namespace IntegralWholeProjectiveProper318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralWholeOrderScalarMaps318 IntegralWholeReciprocalGluing318
open IntegralWholeProjectiveProjection318 IntegralWholeProjectivePreimages318
open IntegralWholeChartFiniteness318
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_square : IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder R c))))
    (finiteChart R c) (JLineAtlas318.chart R 1) (projection R c) := by
  apply IsOpenImmersion.isPullback
  · exact finite_restriction R c
  · exact finite_preimage R c

theorem reciprocal_square : IsPullback
    (Spec.map (CommRingCat.ofHom (infinityProjection R c).toRingHom))
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

/-- Properness and separatedness of the constructed WHOLE-order scheme
follow from its actual finite projective projection over any coefficient ring.
This does not yet identify it with the earlier restricted integral pushout. -/
theorem proper_separated : IsProper (IntegralWholeProjectiveProjection318.structureMap R c) ∧
    IsSeparated (IntegralWholeProjectiveProjection318.structureMap R c) := by
  unfold IntegralWholeProjectiveProjection318.structureMap
  exact ⟨inferInstance,inferInstance⟩
end IntegralWholeProjectiveProper318
