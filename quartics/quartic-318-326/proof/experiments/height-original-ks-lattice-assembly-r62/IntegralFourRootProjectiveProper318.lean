module
public import IntegralFourRootProjectivePreimages318
public import IntegralFourRootChartFiniteness318
public section
noncomputable section
namespace IntegralFourRootProjectiveProper318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralFourRootReciprocalCharts318 IntegralFourRootScalarMaps318 IntegralFourRootGluing318
open IntegralFourRootProjectiveProjection318 IntegralFourRootProjectivePreimages318
open IntegralFourRootChartFiniteness318
set_option maxHeartbeats 1400000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)

theorem finite_square : IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder d a))))
    (finiteChart R d a) (JLineAtlas318.chart R 1) (projection R d a) := by
  apply IsOpenImmersion.isPullback
  · exact finite_restriction R d a
  · exact finite_preimage R d a

theorem reciprocal_square : IsPullback
    (Spec.map (CommRingCat.ofHom (algebraMap R[X] (ReciprocalOrder d a))))
    (infinityChart R d a) (JLineAtlas318.chart R 0) (projection R d a) := by
  apply IsOpenImmersion.isPullback
  · exact reciprocal_restriction R d a
  · exact reciprocal_preimage R d a

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
instance projection_finite : IsFinite (projection R d a) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P:=@IsFinite) (targetCover R)]
  intro i
  fin_cases i
  · change IsFinite (pullback.snd (projection R d a) (JLineAtlas318.chart R 0))
    rw [←(reciprocal_square R d a).flip.isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (projection R d a) (JLineAtlas318.chart R 1))
    rw [←(finite_square R d a).flip.isoPullback_inv_snd]
    infer_instance

/-- Properness and separatedness of the constructed WHOLE-order scheme
follow from its actual finite projective projection over any coefficient ring.
No normality, smoothness, section generation or KS identity follows from this. -/
theorem proper_separated : IsProper (IntegralFourRootProjectiveProjection318.structureMap R d a) ∧
    IsSeparated (IntegralFourRootProjectiveProjection318.structureMap R d a) := by
  unfold IntegralFourRootProjectiveProjection318.structureMap
  exact ⟨inferInstance,inferInstance⟩
end IntegralFourRootProjectiveProper318
