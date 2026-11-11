module
public import NormalizedWholeProjectivePreimages318
public section
noncomputable section
namespace NormalizedWholeProjectiveProper318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NormalizedWholeOverlap318 NormalizedWholeScalarMaps318 NormalizedWholeGluing318
open NormalizedWholeProjection318 NormalizedWholeProjectivePreimages318
open NormalizedWholeChartFinite318
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (d contacts : Fin 4 → R)

theorem finite_square : IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder R d contacts))))
    (finiteChart R d contacts) (JLineAtlas318.chart R 1) (projection R d contacts) := by
  apply IsOpenImmersion.isPullback
  · exact finite_restriction R d contacts
  · exact finite_preimage R d contacts

theorem reciprocal_square : IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (InfinityOrder R d contacts))))
    (infinityChart R d contacts) (JLineAtlas318.chart R 0) (projection R d contacts) := by
  apply IsOpenImmersion.isPullback
  · exact reciprocal_restriction R d contacts
  · exact reciprocal_preimage R d contacts

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
instance projection_finite : IsFinite (projection R d contacts) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P:=@IsFinite) (targetCover R)]
  intro i
  fin_cases i
  · change IsFinite (pullback.snd (projection R d contacts) (JLineAtlas318.chart R 0))
    rw [←(reciprocal_square R d contacts).flip.isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (projection R d contacts) (JLineAtlas318.chart R 1))
    rw [←(finite_square R d contacts).flip.isoPullback_inv_snd]
    infer_instance

/-- Properness and separatedness of the constructed WHOLE-order scheme
follow from its actual finite projective projection over any coefficient ring.
The model may be singular; this is not a normalization or regularity theorem. -/
theorem proper_separated : IsProper (NormalizedWholeProjection318.structureMap R d contacts) ∧
    IsSeparated (NormalizedWholeProjection318.structureMap R d contacts) := by
  unfold NormalizedWholeProjection318.structureMap
  exact ⟨inferInstance,inferInstance⟩
end NormalizedWholeProjectiveProper318
