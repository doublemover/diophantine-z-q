module
public import IntegralPencilFinite318
public section
noncomputable section
namespace IntegralSectionPencilDegree318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

@[expose] def affineMap : IntegralGluedModel318.finiteScheme R c ⟶ Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap R[X] (SourceOrder R c)))

/-- The original full four-root source is the ENTIRE finite-chart preimage
of the original contact pencil, rather than an unrelated rank16 algebra. -/
theorem finite_preimage : IntegralOriginalContactPencil318.projection R c ⁻¹ᵁ
    (JLineAtlas318.chart R 1).opensRange=(IntegralGluedModel318.finiteChart R c).opensRange := by
  ext x
  constructor
  · intro hx
    have hw : IntegralOriginalModelMorphism318.map R c x ∈
        (IntegralWholeReciprocalGluing318.finiteChart R c).opensRange := by
      rw [←IntegralPencilPreimages318.finite_preimage]
      exact hx
    rw [←IntegralOriginalChartsProperCover318.originalSource_range] at hw
    obtain ⟨a,ha⟩ := hw
    refine ⟨a,?_⟩
    apply IntegralOriginalProperModel318.injective R c
    change (IntegralGluedModel318.finiteChart R c ≫ IntegralOriginalModelMorphism318.map R c) a=_
    rw [IntegralOriginalModelMorphism318.finiteChart_map]
    exact ha
  · rintro ⟨a,rfl⟩
    change (IntegralGluedModel318.finiteChart R c ≫ IntegralOriginalContactPencil318.projection R c) a ∈ _
    rw [IntegralOriginalContactPencil318.finite_restriction]
    exact ⟨affineMap R c a,rfl⟩

/-- Exact categorical pullback for the original generating-pair morphism,
including every finite branch point. -/
theorem affine_pullback
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsPullback (affineMap R c) (IntegralGluedModel318.finiteChart R c)
      (JLineAtlas318.chart R 1) (IntegralSectionProjectiveMap318.projectiveMap R c hN) := by
  rw [IntegralSectionProjectiveMap318.projectiveMap_eq]
  apply IsOpenImmersion.isPullback
  · exact IntegralOriginalContactPencil318.finite_restriction R c
  · exact finite_preimage R c

/-- The coordinate algebra of that exact whole affine pullback is finite
free over the ORIGINAL t-line. -/
theorem finite_free : Module.Finite R[X] (SourceOrder R c) ∧ Module.Free R[X] (SourceOrder R c) :=
  FourRootOrder318.finite_free (coefficient R c)

/-- Its rank is sixteen, not the rank8 of the auxiliary y0 projection.
This assertion is attached to the actual entire t-chart pullback above. -/
theorem rank_sixteen [Nontrivial R] : Module.finrank R[X] (SourceOrder R c)=16 :=
  FourRootOrder318.rank_sixteen (coefficient R c)

/-- The original section-defined contact pencil is a finite proper morphism
with the exact full finite free rank16 affine chart. -/
theorem finite_pencil_rank_sixteen [Nontrivial R]
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger:R)) :
    IsFinite (IntegralSectionProjectiveMap318.projectiveMap R c hN) ∧
    IsProper (IntegralSectionProjectiveMap318.projectiveMap R c hN) ∧
    Module.Finite R[X] (SourceOrder R c) ∧ Module.Free R[X] (SourceOrder R c) ∧
    Module.finrank R[X] (SourceOrder R c)=16 := by
  letI := IntegralPencilFinite318.section_pencil_finite R c hN
  exact ⟨inferInstance,inferInstance,(finite_free R c).1,(finite_free R c).2,rank_sixteen R c⟩
end IntegralSectionPencilDegree318
