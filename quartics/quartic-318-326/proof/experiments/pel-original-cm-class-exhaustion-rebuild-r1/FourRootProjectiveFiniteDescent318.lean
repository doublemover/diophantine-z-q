module
public import FourRootProjectiveChartPullbacks318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace FourRootProjectiveFiniteDescent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootGluedScheme318 FourRootProjectiveProjection318 FourRootProjectiveChartPullbacks318
@[expose] def targetCover:(ProjectiveJLine318.scheme ℂ).OpenCover where
  I₀:=Fin 2
  X _:=Spec (CommRingCat.of (Polynomial ℂ))
  f:=JLineAtlas318.chart ℂ
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      have hp:p∈(⊤:(ProjectiveJLine318.scheme ℂ).Opens):=trivial
      rw [←JLineAtlas318.standard_opens_cover ℂ,TopologicalSpace.Opens.mem_iSup] at hp
      obtain ⟨j,hj⟩:=hp
      rw [←JLineAtlas318.chart_range] at hj
      exact ⟨j,hj⟩
    · intro j;infer_instance
variable (b:Fin 4→ℂ)
/-- Affine finiteness is consumed on the ACTUAL Cartesian projective
chart squares. No properness or missing-points assertion is assumed. -/
theorem centered_finite
    (hf:(finiteCoordinate b).toRingHom.Finite)
    (hi:(infinityCoordinate b).toRingHom.Finite):IsFinite (centeredProjection b):=by
  apply IsZariskiLocalAtTarget.of_openCover targetCover
  intro j
  fin_cases j
  · have h:=(infinity_square b).flip
    haveI:IsFinite (Spec.map (CommRingCat.ofHom (infinityCoordinate b).toRingHom)):=
      (IsFinite.SpecMap_iff _).mpr hi
    have hc:IsFinite (h.isoPullback.inv≫
        Spec.map (CommRingCat.ofHom (infinityCoordinate b).toRingHom)):=inferInstance
    simpa only [h.isoPullback_inv_snd] using hc
  · have h:=(finite_square b).flip
    haveI:IsFinite (Spec.map (CommRingCat.ofHom (finiteCoordinate b).toRingHom)):=
      (IsFinite.SpecMap_iff _).mpr hf
    have hc:IsFinite (h.isoPullback.inv≫
        Spec.map (CommRingCat.ofHom (finiteCoordinate b).toRingHom)):=inferInstance
    simpa only [h.isoPullback_inv_snd] using hc

theorem projection_finite
    (hf:(finiteCoordinate b).toRingHom.Finite)
    (hi:(infinityCoordinate b).toRingHom.Finite):
    IsFinite (FourRootProjectiveProjection318.projection b):=by
  letI:=centered_finite b hf hi
  change IsFinite (centeredProjection b≫(ProjectiveAffineLine318.iso ℂ 1 (b 0)).hom)
  infer_instance

theorem structure_proper
    (hf:(finiteCoordinate b).toRingHom.Finite)
    (hi:(infinityCoordinate b).toRingHom.Finite):IsProper (structureMap b):=by
  letI:=projection_finite b hf hi
  rw [←over_base]
  infer_instance
end FourRootProjectiveFiniteDescent318
