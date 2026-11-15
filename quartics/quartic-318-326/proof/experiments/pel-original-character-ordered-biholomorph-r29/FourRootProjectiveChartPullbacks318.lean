module
public import FourRootProjectiveProjection318
public import ProjectiveLineComplexChartGeometry318
public section
noncomputable section
namespace FourRootProjectiveChartPullbacks318
open AlgebraicGeometry CategoryTheory Polynomial MvPolynomial HomogeneousLocalization
open FourRootGluedScheme318 FourRootCoordinateOverlap318 FourRootProjectiveProjection318
attribute [local instance] MvPolynomial.gradedAlgebra
variable (b:Fin 4→ℂ)

lemma intoInfinity_range:(intoInfinity b).opensRange=
    PrimeSpectrum.basicOpen (FourRootInfinityCoordinateRing318.coordinate b none):=by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range _ _
lemma intoFinite_range:(intoFinite b).opensRange=
    PrimeSpectrum.basicOpen (FourRootAffineCoordinateRing318.coordinate b (some 0)):=by
  unfold intoFinite
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range _ _

/-- Literal localization intersection recovered on ALL prime-spectrum
points of the genuine pushout, not just complex closed points. -/
lemma infinity_preimage_finite:infinityChart b ⁻¹ᵁ(finiteChart b).opensRange=
    (intoInfinity b).opensRange:=by
  ext p
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨z,hz,hp⟩:=GenericOpenPushout318.exists_overlap
      (intoFinite b) (intoInfinity b) q p hq
    exact ⟨z,hp⟩
  · rintro ⟨z,rfl⟩
    refine ⟨intoFinite b z,?_⟩
    exact congrArg (fun f=>f z) (chart_overlap b)
lemma finite_preimage_infinity:finiteChart b ⁻¹ᵁ(infinityChart b).opensRange=
    (intoFinite b).opensRange:=by
  ext p
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨z,hp,hz⟩:=GenericOpenPushout318.exists_overlap
      (intoFinite b) (intoInfinity b) p q hq.symm
    exact ⟨z,hp⟩
  · rintro ⟨z,rfl⟩
    refine ⟨intoInfinity b z,?_⟩
    exact congrArg (fun f=>f z) (chart_overlap b).symm

lemma chart_one_preimage_zero:
    JLineAtlas318.chart ℂ 1 ⁻¹ᵁ(JLineAtlas318.chart ℂ 0).opensRange=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial ℂ):=by
  rw [JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading ℂ)
    (MvPolynomial.isHomogeneous_X ℂ (1:Fin 2)) (by omega)
    (MvPolynomial.isHomogeneous_X ℂ (0:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv ℂ 1)
    (Away.isLocalizationElem (MvPolynomial.isHomogeneous_X ℂ (1:Fin 2))
      (MvPolynomial.isHomogeneous_X ℂ (0:Fin 2))))=_
  have h:Away.isLocalizationElem (MvPolynomial.isHomogeneous_X ℂ (1:Fin 2))
      (MvPolynomial.isHomogeneous_X ℂ (0:Fin 2))=(JLineAtlas318.chartEquiv ℂ 1).symm Polynomial.X:=by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

lemma centered_preimage_one:centeredProjection b ⁻¹ᵁ(JLineAtlas318.chart ℂ 1).opensRange=
    (finiteChart b).opensRange:=by
  ext p
  rcases charts_cover b p with ⟨p,rfl⟩|⟨p,rfl⟩
  · have hp:centeredProjection b (finiteChart b p)∈(JLineAtlas318.chart ℂ 1).opensRange:=by
      refine ⟨Spec.map (CommRingCat.ofHom (finiteCoordinate b).toRingHom) p,?_⟩
      exact congrArg (fun f=>f p) (finite_centered b).symm
    exact iff_of_true hp ⟨p,rfl⟩
  · change p∈infinityChart b ⁻¹ᵁ(centeredProjection b ⁻¹ᵁ_) ↔
      p∈infinityChart b ⁻¹ᵁ(finiteChart b).opensRange
    rw [←Scheme.Hom.comp_preimage,infinity_centered,infinityProjection,
      Scheme.Hom.comp_preimage,ProjectiveLineComplexChartGeometry318.chart_zero_preimage_one,
      SpecMap_preimage_basicOpen,infinity_preimage_finite,intoInfinity_range]
    simp only [infinityCoordinate,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Polynomial.aeval_X,PrimeSpectrum.basicOpen_pow _ 2 (by decide)]
lemma centered_preimage_zero:centeredProjection b ⁻¹ᵁ(JLineAtlas318.chart ℂ 0).opensRange=
    (infinityChart b).opensRange:=by
  ext p
  rcases charts_cover b p with ⟨p,rfl⟩|⟨p,rfl⟩
  · change p∈finiteChart b ⁻¹ᵁ(centeredProjection b ⁻¹ᵁ_) ↔
      p∈finiteChart b ⁻¹ᵁ(infinityChart b).opensRange
    rw [←Scheme.Hom.comp_preimage,finite_centered,finiteProjection,
      Scheme.Hom.comp_preimage,chart_one_preimage_zero,
      SpecMap_preimage_basicOpen,finite_preimage_infinity,intoFinite_range]
    simp only [finiteCoordinate,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
    rw [←FourRootAffineCoordinateRing318.relation b 0,
      PrimeSpectrum.basicOpen_pow _ 2 (by decide)]
  · have hp:centeredProjection b (infinityChart b p)∈(JLineAtlas318.chart ℂ 0).opensRange:=by
      refine ⟨Spec.map (CommRingCat.ofHom (infinityCoordinate b).toRingHom) p,?_⟩
      exact congrArg (fun f=>f p) (infinity_centered b).symm
    exact iff_of_true hp ⟨p,rfl⟩

/-- Both affine coordinate maps are the actual projective base-change
charts, retaining their complete scheme structure. -/
theorem finite_square:IsPullback
    (Spec.map (CommRingCat.ofHom (finiteCoordinate b).toRingHom)) (finiteChart b)
    (JLineAtlas318.chart ℂ 1) (centeredProjection b):=
  IsOpenImmersion.isPullback _ _ _ _ (finite_centered b).symm (centered_preimage_one b)
theorem infinity_square:IsPullback
    (Spec.map (CommRingCat.ofHom (infinityCoordinate b).toRingHom)) (infinityChart b)
    (JLineAtlas318.chart ℂ 0) (centeredProjection b):=
  IsOpenImmersion.isPullback _ _ _ _ (infinity_centered b).symm (centered_preimage_zero b)
end FourRootProjectiveChartPullbacks318
