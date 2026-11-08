module
public import JLineOverlap318
public import JLineOverlapOpen318
public section
noncomputable section
namespace ProjectiveLineOverlap318
open AlgebraicGeometry CategoryTheory Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev A := Localization.Away (X:ℚ[X])
@[expose] def t : A := algebraMap ℚ[X] A X
@[expose] def tUnit : Aˣ := (IsLocalization.Away.algebraMap_isUnit (X:ℚ[X]) (S:=A)).unit

theorem tUnit_coe : (tUnit:A)=t := IsLocalization.Away.algebraMap_isUnit (X:ℚ[X]) |>.unit_spec
@[expose] def s : A := ↑tUnit⁻¹
@[expose] def finiteInclusion : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] A))
@[expose] def infinityInclusion : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval s).toRingHom)
instance finite_open : IsOpenImmersion finiteInclusion := by
  unfold finiteInclusion A
  infer_instance

theorem maps_agree : finiteInclusion ≫ JLineAtlas318.chart ℚ 1=
    infinityInclusion ≫ JLineAtlas318.chart ℚ 0 := by
  have he : (Polynomial.aeval (↑tUnit:A)).toRingHom=algebraMap ℚ[X] A := by
    apply Polynomial.ringHom_ext
    · intro q
      simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,Polynomial.algebraMap_eq] using
        (IsScalarTower.algebraMap_apply ℚ ℚ[X] A q)
    · simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,t] using tUnit_coe
  simpa only [he,finiteInclusion,infinityInclusion,s] using
    (JLineOverlap318.unit_chart_overlap (R:=ℚ) tUnit)

@[expose] def embedding : Spec (CommRingCat.of A) ⟶ ProjectiveJLine318.scheme ℚ :=
  finiteInclusion ≫ JLineAtlas318.chart ℚ 1
instance embedding_open : IsOpenImmersion embedding := by unfold embedding; infer_instance
instance infinity_open : IsOpenImmersion infinityInclusion := by
  haveI : IsOpenImmersion (infinityInclusion ≫ JLineAtlas318.chart ℚ 0) := by
    rw [←maps_agree]
    infer_instance
  exact IsOpenImmersion.of_comp infinityInclusion (JLineAtlas318.chart ℚ 0)

theorem finite_range : finiteInclusion.opensRange=PrimeSpectrum.basicOpen (X:ℚ[X]) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range A (X:ℚ[X])

theorem chart_one_preimage_zero :
    JLineAtlas318.chart ℚ 1 ⁻¹ᵁ (JLineAtlas318.chart ℚ 0 ''ᵁ ⊤)=
      PrimeSpectrum.basicOpen (X:ℚ[X]) := by
  rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading ℚ)
    (MvPolynomial.isHomogeneous_X ℚ (1:Fin 2)) (by omega)
    (MvPolynomial.isHomogeneous_X ℚ (0:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv ℚ 1)
    (HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X ℚ (1:Fin 2))
      (MvPolynomial.isHomogeneous_X ℚ (0:Fin 2))))=_
  have h : HomogeneousLocalization.Away.isLocalizationElem (MvPolynomial.isHomogeneous_X ℚ (1:Fin 2))
      (MvPolynomial.isHomogeneous_X ℚ (0:Fin 2))=
      (JLineAtlas318.chartEquiv ℚ 1).symm X := by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [HomogeneousLocalization.Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

theorem full_intersection :
    (JLineAtlas318.chart ℚ 1).opensRange ⊓ (JLineAtlas318.chart ℚ 0).opensRange=embedding.opensRange := by
  rw [←Scheme.Hom.image_preimage_eq_opensRange_inf,
    ←Scheme.Hom.image_top_eq_opensRange (JLineAtlas318.chart ℚ 0),chart_one_preimage_zero,
    ←finite_range,←Scheme.Hom.opensRange_comp]
  rfl

theorem actual_pullback : IsPullback infinityInclusion finiteInclusion
    (JLineAtlas318.chart ℚ 0) (JLineAtlas318.chart ℚ 1) := by
  apply IsOpenImmersion.isPullback
  · exact maps_agree
  · rw [←Scheme.Hom.image_top_eq_opensRange,chart_one_preimage_zero,finite_range]

theorem ts : t*s=1 := by simpa only [←tUnit_coe,s] using Units.mul_inv tUnit
end ProjectiveLineOverlap318
