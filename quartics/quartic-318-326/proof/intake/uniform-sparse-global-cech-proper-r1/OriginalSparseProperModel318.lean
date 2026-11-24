module
public import OriginalSparseP1ChartPullbacks318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! Properness of the actual sparse genus-two model, not an assumed
valuative extension property of a comparison model. -/
public section
noncomputable section
namespace OriginalSparseProperModel318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalSparseGluedScheme318 OriginalSparseP1Projection318
open OriginalSparseP1ChartPullbacks318 OriginalSparseQuadraticCharts318
universe u
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] (s t : R)

@[expose] def targetCover : (ProjectiveJLine318.scheme R).OpenCover where
  I₀ := Fin 2
  X _ := Spec (CommRingCat.of (Polynomial R))
  f := JLineAtlas318.chart R
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      have hp : p ∈ (⊤ : (ProjectiveJLine318.scheme R).Opens) := trivial
      rw [←JLineAtlas318.standard_opens_cover R,TopologicalSpace.Opens.mem_iSup] at hp
      obtain ⟨j,hj⟩ := hp
      rw [←JLineAtlas318.chart_range] at hj
      exact ⟨j,hj⟩
    · intro j
      infer_instance

theorem projection_finite : IsFinite (projection s t) := by
  apply IsZariskiLocalAtTarget.of_openCover (P:=@IsFinite) (targetCover (R:=R))
  intro j
  change Fin 2 at j
  change IsFinite (pullback.snd (projection s t) (JLineAtlas318.chart R j))
  fin_cases j
  · change IsFinite (pullback.snd (projection s t) (JLineAtlas318.chart R 0))
    have h := (infinity_square s t).flip
    have : IsFinite (Spec.map (CommRingCat.ofHom (infinityCoordinate s t).toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr (coordinate_finite (G s t))
    have hc : IsFinite (h.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (infinityCoordinate s t).toRingHom)) := inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
  · change IsFinite (pullback.snd (projection s t) (JLineAtlas318.chart R 1))
    have h := (finite_square s t).flip
    have : IsFinite (Spec.map (CommRingCat.ofHom (finiteCoordinate s t).toRingHom)) :=
      (IsFinite.SpecMap_iff _).mpr (coordinate_finite (F s t))
    have hc : IsFinite (h.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (finiteCoordinate s t).toRingHom)) := inferInstance
    simpa only [h.isoPullback_inv_snd] using hc

theorem structure_proper : IsProper (structureMap s t) := by
  let := projection_finite s t
  rw [←over_base]
  infer_instance

end OriginalSparseProperModel318

#print axioms OriginalSparseProperModel318.structure_proper
