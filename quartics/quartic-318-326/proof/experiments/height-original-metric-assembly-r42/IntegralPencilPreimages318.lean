module
public import IntegralPencilChartFiniteness318
public section
noncomputable section
namespace IntegralPencilPreimages318
open Polynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralPencilScalarMaps318 IntegralWholeReciprocalGluing318
open IntegralWholePencilMap318 IntegralWholeOpenRanges318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

lemma basicOpen_square {A : Type*} [CommRing A] (x : A) :
    PrimeSpectrum.basicOpen (x^2)=PrimeSpectrum.basicOpen x := by
  ext p
  change (x^2∉p.asIdeal)↔(x∉p.asIdeal)
  rw [pow_two,p.isPrime.mul_mem_iff]
  tauto

theorem finite_cross : finiteProjection R c ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange=
    (intoFinite R c).opensRange := by
  rw [finiteProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 0),
    IntegralProjectiveChartIntersection318.chart_one_preimage_zero,
    SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (finiteCoordinate R c X)=_
  rw [finiteCoordinate,Polynomial.aeval_X,PrimeSpectrum.basicOpen_mul,
    IntegralWholeProjectivePreimages318.basicOpen_unit _
      (((c 0)⁻¹).isUnit.map (algebraMap R (FiniteOrder R c))),top_inf_eq,basicOpen_square]
  exact (finite_range R c).symm

theorem reciprocal_cross : reciprocalProjection R c ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
    (intoInfinity R c).opensRange := by
  rw [reciprocalProjection,Scheme.Hom.comp_preimage,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart R 1),
    IntegralProjectiveChartIntersection318.chart_zero_preimage_one,
    SpecMap_preimage_basicOpen]
  change PrimeSpectrum.basicOpen (reciprocalCoordinate R c X)=_
  rw [reciprocalCoordinate,Polynomial.aeval_X,PrimeSpectrum.basicOpen_mul,
    IntegralWholeProjectivePreimages318.basicOpen_unit _ (((c 0)⁻¹).isUnit.map (algebraMap R (InfinityOrder R c))),top_inf_eq,basicOpen_square]
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
    exact ⟨Spec.map (CommRingCat.ofHom (finiteCoordinate R c).toRingHom) a,rfl⟩

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
    exact ⟨Spec.map (CommRingCat.ofHom (reciprocalCoordinate R c).toRingHom) b,rfl⟩

end IntegralPencilPreimages318
