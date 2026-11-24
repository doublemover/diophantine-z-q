module
public import OriginalSparseP1Projection318
public section
noncomputable section
namespace OriginalSparseP1ChartPullbacks318
open AlgebraicGeometry CategoryTheory Polynomial MvPolynomial HomogeneousLocalization
open OriginalSparseGluedScheme318 OriginalSparseQuadraticCharts318 OriginalSparseP1Projection318
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R : Type u} [CommRing R] (s t : R)

lemma intoInfinity_range:(intoInfinity s t).opensRange=
    PrimeSpectrum.basicOpen (x (G s t)):=by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range _ _
lemma intoFinite_range:(intoFinite s t).opensRange=
    PrimeSpectrum.basicOpen (x (F s t)):=by
  unfold intoFinite
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- Literal localization intersection recovered on ALL prime-spectrum
points of the genuine pushout, not just complex closed points. -/
lemma infinity_preimage_finite:infinityChart s t ⁻¹ᵁ(finiteChart s t).opensRange=
    (intoInfinity s t).opensRange:=by
  ext p
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨z,hz,hp⟩:=GenericOpenPushout318.exists_overlap
      (intoFinite s t) (intoInfinity s t) q p hq
    exact ⟨z,hp⟩
  · rintro ⟨z,rfl⟩
    refine ⟨intoFinite s t z,?_⟩
    exact congrArg (fun f=>f z) (chart_overlap s t)
lemma finite_preimage_infinity:finiteChart s t ⁻¹ᵁ(infinityChart s t).opensRange=
    (intoFinite s t).opensRange:=by
  ext p
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨z,hp,hz⟩:=GenericOpenPushout318.exists_overlap
      (intoFinite s t) (intoInfinity s t) p q hq.symm
    exact ⟨z,hp⟩
  · rintro ⟨z,rfl⟩
    refine ⟨intoInfinity s t z,?_⟩
    exact congrArg (fun f=>f z) (chart_overlap s t).symm

lemma chart_one_preimage_zero:
    JLineAtlas318.chart R 1 ⁻¹ᵁ(JLineAtlas318.chart R 0).opensRange=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial R):=by
  rw [JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (MvPolynomial.isHomogeneous_X R (1:Fin 2)) (by omega)
    (MvPolynomial.isHomogeneous_X R (0:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 1)
    (Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (1:Fin 2))
      (MvPolynomial.isHomogeneous_X R (0:Fin 2))))=_
  have h:Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (1:Fin 2))
      (MvPolynomial.isHomogeneous_X R (0:Fin 2))=(JLineAtlas318.chartEquiv R 1).symm Polynomial.X:=by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

lemma chart_zero_preimage_one:
    JLineAtlas318.chart R 0 ⁻¹ᵁ(JLineAtlas318.chart R 1).opensRange=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial R):=by
  rw [JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (MvPolynomial.isHomogeneous_X R (0:Fin 2)) (by omega)
    (MvPolynomial.isHomogeneous_X R (1:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 0)
    (Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (0:Fin 2))
      (MvPolynomial.isHomogeneous_X R (1:Fin 2))))=_
  have h:Away.isLocalizationElem (MvPolynomial.isHomogeneous_X R (0:Fin 2))
      (MvPolynomial.isHomogeneous_X R (1:Fin 2))=(JLineAtlas318.chartEquiv R 0).symm Polynomial.X:=by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

lemma centered_preimage_one:projection s t ⁻¹ᵁ(JLineAtlas318.chart R 1).opensRange=
    (finiteChart s t).opensRange:=by
  ext p
  rcases charts_cover s t p with ⟨p,rfl⟩|⟨p,rfl⟩
  · have hp:projection s t (finiteChart s t p)∈(JLineAtlas318.chart R 1).opensRange:=by
      refine ⟨Spec.map (CommRingCat.ofHom (finiteCoordinate s t).toRingHom) p,?_⟩
      exact congrArg (fun f=>f p) (finite_projection s t).symm
    exact iff_of_true hp ⟨p,rfl⟩
  · suffices h : infinityChart s t ⁻¹ᵁ (projection s t ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange) =
        infinityChart s t ⁻¹ᵁ (finiteChart s t).opensRange by
      exact SetLike.ext_iff.mp h p
    rw [←Scheme.Hom.comp_preimage,infinity_projection,infinityProjection,
      Scheme.Hom.comp_preimage,chart_zero_preimage_one,
      SpecMap_preimage_basicOpen,infinity_preimage_finite,intoInfinity_range]
    exact congrArg PrimeSpectrum.basicOpen (Polynomial.aeval_X (x (G s t)))
lemma centered_preimage_zero:projection s t ⁻¹ᵁ(JLineAtlas318.chart R 0).opensRange=
    (infinityChart s t).opensRange:=by
  ext p
  rcases charts_cover s t p with ⟨p,rfl⟩|⟨p,rfl⟩
  · suffices h : finiteChart s t ⁻¹ᵁ (projection s t ⁻¹ᵁ (JLineAtlas318.chart R 0).opensRange) =
        finiteChart s t ⁻¹ᵁ (infinityChart s t).opensRange by
      exact SetLike.ext_iff.mp h p
    rw [←Scheme.Hom.comp_preimage,finite_projection,finiteProjection,
      Scheme.Hom.comp_preimage,chart_one_preimage_zero,
      SpecMap_preimage_basicOpen,finite_preimage_infinity,intoFinite_range]
    exact congrArg PrimeSpectrum.basicOpen (Polynomial.aeval_X (x (F s t)))
  · have hp:projection s t (infinityChart s t p)∈(JLineAtlas318.chart R 0).opensRange:=by
      refine ⟨Spec.map (CommRingCat.ofHom (infinityCoordinate s t).toRingHom) p,?_⟩
      exact congrArg (fun f=>f p) (infinity_projection s t).symm
    exact iff_of_true hp ⟨p,rfl⟩

/-- Both affine coordinate maps are the actual projective base-change
charts, retaining their complete scheme structure. -/
theorem finite_square:IsPullback
    (Spec.map (CommRingCat.ofHom (finiteCoordinate s t).toRingHom)) (finiteChart s t)
    (JLineAtlas318.chart R 1) (projection s t):=
  IsOpenImmersion.isPullback _ _ _ _ (finite_projection s t) (centered_preimage_one s t)
theorem infinity_square:IsPullback
    (Spec.map (CommRingCat.ofHom (infinityCoordinate s t).toRingHom)) (infinityChart s t)
    (JLineAtlas318.chart R 0) (projection s t):=
  IsOpenImmersion.isPullback _ _ _ _ (infinity_projection s t) (centered_preimage_zero s t)
end OriginalSparseP1ChartPullbacks318
