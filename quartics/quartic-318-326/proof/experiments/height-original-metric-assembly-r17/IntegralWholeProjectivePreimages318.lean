module
public import IntegralProjectiveChartIntersection318
public section
noncomputable section
namespace IntegralWholeProjectivePreimages318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralWholeOrderScalarMaps318 IntegralWholeReciprocalGluing318
open IntegralWholeProjectiveProjection318 IntegralWholeOpenRanges318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

lemma basicOpen_unit {A : Type*} [CommRing A] (x : A) (hx : IsUnit x) :
    PrimeSpectrum.basicOpen x=⊤ := by
  ext p
  change (x∉p.asIdeal)↔True
  constructor
  · intro _;trivial
  · intro _ h
    exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem h hx)

theorem finite_cross : finiteProjection R c ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (intoFinite R c).opensRange := by
  rw [finiteProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 0),
    IntegralProjectiveChartIntersection318.chart_one_preimage_zero,
    SpecMap_preimage_basicOpen]
  exact (finite_range R c).symm

theorem reciprocal_cross : reciprocalProjection R c ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (intoInfinity R c).opensRange := by
  rw [reciprocalProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 1),
    IntegralProjectiveChartIntersection318.chart_zero_preimage_one,
    SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (infinityProjection R c X)=_
  rw [infinityProjection,Polynomial.aeval_X,PrimeSpectrum.basicOpen_mul,
    basicOpen_unit _ (((c 0)⁻¹).isUnit.map (algebraMap R (InfinityOrder R c))),top_inf_eq]
  exact (infinity_range R c).symm

/-- The whole finite order is the ENTIRE preimage of the finite target
chart, not merely an affine open lying over it. -/
theorem finite_preimage : projection R c ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (finiteChart R c).opensRange := by
  ext x
  change (projection R c x ∈ Set.range (JLineAtlas318.chart R 1)) ↔
    x ∈ Set.range (finiteChart R c)
  constructor
  · intro hx
    obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := charts_cover R c x
    · exact ⟨a,rfl⟩
    · have hb : b ∈ reciprocalProjection R c ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange := by
        change reciprocalProjection R c b ∈ Set.range (JLineAtlas318.chart R 1)
        have h := congrArg (fun f => f b) (reciprocal_restriction R c)
        exact h ▸ hx
      rw [reciprocal_cross] at hb
      obtain ⟨q,hq⟩ := hb
      refine ⟨intoFinite R c q,?_⟩
      calc
        finiteChart R c (intoFinite R c q)=infinityChart R c (intoInfinity R c q) :=
          congrArg (fun f => f q) (pushout.condition (f:=intoFinite R c) (g:=intoInfinity R c))
        _ = infinityChart R c b := congrArg (infinityChart R c) hq
  · rintro ⟨a,rfl⟩
    have h := congrArg (fun f => f a) (finite_restriction R c)
    rw [h]
    exact ⟨Spec.map (CommRingCat.ofHom (algebraMap R[X] (FiniteOrder R c))) a,rfl⟩

/-- The whole reciprocal order is likewise the entire reciprocal target
preimage, including its branch points. -/
theorem reciprocal_preimage : projection R c ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (infinityChart R c).opensRange := by
  ext x
  change (projection R c x ∈ Set.range (JLineAtlas318.chart R 0)) ↔
    x ∈ Set.range (infinityChart R c)
  constructor
  · intro hx
    obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := charts_cover R c x
    · have ha : a ∈ finiteProjection R c ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange := by
        change finiteProjection R c a ∈ Set.range (JLineAtlas318.chart R 0)
        have h := congrArg (fun f => f a) (finite_restriction R c)
        exact h ▸ hx
      rw [finite_cross] at ha
      obtain ⟨q,hq⟩ := ha
      refine ⟨intoInfinity R c q,?_⟩
      calc
        infinityChart R c (intoInfinity R c q)=finiteChart R c (intoFinite R c q) :=
          congrArg (fun f => f q) (pushout.condition (f:=intoFinite R c) (g:=intoInfinity R c)).symm
        _ = finiteChart R c a := congrArg (finiteChart R c) hq
    · exact ⟨b,rfl⟩
  · rintro ⟨b,rfl⟩
    have h := congrArg (fun f => f b) (reciprocal_restriction R c)
    rw [h]
    exact ⟨Spec.map (CommRingCat.ofHom (infinityProjection R c).toRingHom) b,rfl⟩

end IntegralWholeProjectivePreimages318
