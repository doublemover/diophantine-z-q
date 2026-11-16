module
public import IntegralProjectiveChartIntersection318
public import IntegralFourRootOpenRanges318
public import IntegralFourRootProjectiveProjection318
public section
noncomputable section
namespace IntegralFourRootProjectivePreimages318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralFourRootReciprocalCharts318 IntegralFourRootScalarMaps318 IntegralFourRootGluing318
open IntegralFourRootProjectiveProjection318 IntegralFourRootOpenRanges318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

lemma basicOpen_unit {A : Type*} [CommRing A] (x : A) (hx : IsUnit x) :
    PrimeSpectrum.basicOpen x=⊤ := by
  ext p
  change (x∉p.asIdeal)↔True
  constructor
  · intro _;trivial
  · intro _ h
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h hx)

theorem finite_cross : finiteProjection R d a ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (intoFinite R d a).opensRange := by
  rw [finiteProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 0),
    IntegralProjectiveChartIntersection318.chart_one_preimage_zero,
    SpecMap_preimage_basicOpen]
  exact (finite_range R d a).symm

theorem reciprocal_cross : reciprocalProjection R d a ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (intoInfinity R d a).opensRange := by
  rw [reciprocalProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 1),
    IntegralProjectiveChartIntersection318.chart_zero_preimage_one,
    SpecMap_preimage_basicOpen]

  exact (infinity_range R d a).symm

/-- The whole finite order is the ENTIRE preimage of the finite target
chart, not merely an affine open lying over it. -/
theorem finite_preimage : projection R d a ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (finiteChart R d a).opensRange := by
  ext x
  change (projection R d a x ∈ Set.range (JLineAtlas318.chart R 1)) ↔
    x ∈ Set.range (finiteChart R d a)
  constructor
  · intro hx
    obtain ⟨p,rfl⟩ | ⟨b,rfl⟩ := charts_cover R d a x
    · exact ⟨p,rfl⟩
    · have hb : b ∈ reciprocalProjection R d a ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange := by
        change reciprocalProjection R d a b ∈ Set.range (JLineAtlas318.chart R 1)
        have h := congrArg (fun f => f b) (reciprocal_restriction R d a)
        exact h ▸ hx
      rw [reciprocal_cross] at hb
      obtain ⟨q,hq⟩ := hb
      refine ⟨intoFinite R d a q,?_⟩
      calc
        finiteChart R d a (intoFinite R d a q)=infinityChart R d a (intoInfinity R d a q) :=
          congrArg (fun f => f q) (pushout.condition (f:=intoFinite R d a) (g:=intoInfinity R d a))
        _ = infinityChart R d a b := congrArg (infinityChart R d a) hq
  · rintro ⟨p,rfl⟩
    have h := congrArg (fun f => f p) (finite_restriction R d a)
    change projection R d a (finiteChart R d a p) = finiteProjection R d a p at h
    rw [h]
    exact ⟨Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder d a))) p,rfl⟩

/-- The whole reciprocal order is likewise the entire reciprocal target
preimage, including its branch points. -/
theorem reciprocal_preimage : projection R d a ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (infinityChart R d a).opensRange := by
  ext x
  change (projection R d a x ∈ Set.range (JLineAtlas318.chart R 0)) ↔
    x ∈ Set.range (infinityChart R d a)
  constructor
  · intro hx
    obtain ⟨p,rfl⟩ | ⟨b,rfl⟩ := charts_cover R d a x
    · have ha : p ∈ finiteProjection R d a ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange := by
        change finiteProjection R d a p ∈ Set.range (JLineAtlas318.chart R 0)
        have h := congrArg (fun f => f p) (finite_restriction R d a)
        exact h ▸ hx
      rw [finite_cross] at ha
      obtain ⟨q,hq⟩ := ha
      refine ⟨intoInfinity R d a q,?_⟩
      calc
        infinityChart R d a (intoInfinity R d a q)=finiteChart R d a (intoFinite R d a q) :=
          congrArg (fun f => f q) (pushout.condition (f:=intoFinite R d a) (g:=intoInfinity R d a)).symm
        _ = finiteChart R d a p := congrArg (finiteChart R d a) hq
    · exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    have h := congrArg (fun f => f b) (reciprocal_restriction R d a)
    change projection R d a (infinityChart R d a b) = reciprocalProjection R d a b at h
    rw [h]
    exact ⟨Spec.map (CommRingCat.ofHom (algebraMap R[X] (ReciprocalOrder d a))) b,rfl⟩

end IntegralFourRootProjectivePreimages318
