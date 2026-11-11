module
public import NormalizedProjectiveChartIntersection318
public section
noncomputable section
namespace NormalizedWholeProjectivePreimages318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NormalizedWholeOverlap318 NormalizedWholeScalarMaps318 NormalizedWholeGluing318
open NormalizedWholeProjection318 NormalizedWholeOpenRanges318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (d contacts : Fin 4 → R)

lemma basicOpen_unit {A : Type*} [CommRing A] (x : A) (hx : IsUnit x) :
    PrimeSpectrum.basicOpen x=⊤ := by
  ext p
  change (x∉p.asIdeal)↔True
  constructor
  · intro _;trivial
  · intro _ h
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h hx)

theorem finite_cross : finiteProjection R d contacts ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (intoFinite R d contacts).opensRange := by
  rw [finiteProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 0),
    NormalizedProjectiveChartIntersection318.chart_one_preimage_zero,
    SpecMap_preimage_basicOpen]
  exact (finite_range R d contacts).symm

theorem reciprocal_cross : reciprocalProjection R d contacts ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (intoInfinity R d contacts).opensRange := by
  rw [reciprocalProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 1),
    NormalizedProjectiveChartIntersection318.chart_zero_preimage_one,
    SpecMap_preimage_basicOpen]
  exact (infinity_range R d contacts).symm

/-- The whole finite order is the ENTIRE preimage of the finite target
chart, not merely an affine open lying over it. -/
theorem finite_preimage : projection R d contacts ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (finiteChart R d contacts).opensRange := by
  ext x
  change (projection R d contacts x ∈ Set.range (JLineAtlas318.chart R 1)) ↔
    x ∈ Set.range (finiteChart R d contacts)
  constructor
  · intro hx
    obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := charts_cover R d contacts x
    · exact ⟨a,rfl⟩
    · have hb : b ∈ reciprocalProjection R d contacts ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange := by
        change reciprocalProjection R d contacts b ∈ Set.range (JLineAtlas318.chart R 1)
        have h := congrArg (fun f => f b) (reciprocal_restriction R d contacts)
        exact h ▸ hx
      rw [reciprocal_cross] at hb
      obtain ⟨q,hq⟩ := hb
      refine ⟨intoFinite R d contacts q,?_⟩
      calc
        finiteChart R d contacts (intoFinite R d contacts q)=infinityChart R d contacts (intoInfinity R d contacts q) :=
          congrArg (fun f => f q) (pushout.condition (f:=intoFinite R d contacts) (g:=intoInfinity R d contacts))
        _ = infinityChart R d contacts b := congrArg (infinityChart R d contacts) hq
  · rintro ⟨a,rfl⟩
    have h := congrArg (fun f => f a) (finite_restriction R d contacts)
    rw [h]
    exact ⟨Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder R d contacts))) a,rfl⟩

/-- The whole reciprocal order is likewise the entire reciprocal target
preimage, including its branch points. -/
theorem reciprocal_preimage : projection R d contacts ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (infinityChart R d contacts).opensRange := by
  ext x
  change (projection R d contacts x ∈ Set.range (JLineAtlas318.chart R 0)) ↔
    x ∈ Set.range (infinityChart R d contacts)
  constructor
  · intro hx
    obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := charts_cover R d contacts x
    · have ha : a ∈ finiteProjection R d contacts ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange := by
        change finiteProjection R d contacts a ∈ Set.range (JLineAtlas318.chart R 0)
        have h := congrArg (fun f => f a) (finite_restriction R d contacts)
        exact h ▸ hx
      rw [finite_cross] at ha
      obtain ⟨q,hq⟩ := ha
      refine ⟨intoInfinity R d contacts q,?_⟩
      calc
        infinityChart R d contacts (intoInfinity R d contacts q)=finiteChart R d contacts (intoFinite R d contacts q) :=
          congrArg (fun f => f q) (pushout.condition (f:=intoFinite R d contacts) (g:=intoInfinity R d contacts)).symm
        _ = finiteChart R d contacts a := congrArg (finiteChart R d contacts) hq
    · exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    have h := congrArg (fun f => f b) (reciprocal_restriction R d contacts)
    rw [h]
    exact ⟨Spec.map (CommRingCat.ofHom (algebraMap R[X] (InfinityOrder R d contacts))) b,rfl⟩

end NormalizedWholeProjectivePreimages318
