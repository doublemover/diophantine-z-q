module
public import SelectedOriginalGenericCompactNormal318
public import SelectedOriginalGenericClosureOverlap318
public import NormalizationBaseCompatibility318
public import JLineOverlapOpen318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericCompactNormal318
open SelectedOriginalGenericClosureOverlap318

namespace SelectedOriginalGenericCompactCharts318

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K] [Algebra JField K]
  [aK : Algebra ℚ K] [hTower : IsScalarTower ℚ JField K]

include aK hTower in
/-- Exact affine chart readout of the actual global normalization. -/
@[expose] def actualSections (i : Fin 2) : chartRing K i ≃+* Order K i :=
  InfinityGlobalChart318.sectionsEquiv_of_factor
    (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℚ i)
    (genericMap K) (genericMap_factor K i)

include aK hTower in
@[expose] def chartEmbedding (i : Fin 2) : Spec (CommRingCat.of (Order K i)) ⟶ model K :=
  Spec.map (CommRingCat.ofHom (actualSections K i).toRingHom) ≫ (sourceCover K i).2.fromSpec

private theorem spec_ringEquiv_isIso {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  let E := Scheme.Spec.mapIso e.toCommRingCatIso.op
  change IsIso E.hom
  exact inferInstance

instance chartSpec_isIso (i : Fin 2) :
    IsIso (Spec.map (CommRingCat.ofHom (actualSections K i).toRingHom)) :=
  spec_ringEquiv_isIso (actualSections K i)

instance (i : Fin 2) : IsOpenImmersion (chartEmbedding K i) := by
  let f := Spec.map (CommRingCat.ofHom (actualSections K i).toRingHom)
  let g := (sourceCover K i).2.fromSpec
  letI : IsIso f := chartSpec_isIso K i
  letI : IsOpenImmersion f := inferInstance
  letI : IsOpenImmersion g := (sourceCover K i).2.isOpenImmersion_fromSpec
  change IsOpenImmersion (f ≫ g)
  exact IsOpenImmersion.comp f g

theorem chartEmbedding_range (i : Fin 2) :
    (chartEmbedding K i).opensRange = (sourceCover K i).1 := by
  let f := Spec.map (CommRingCat.ofHom (actualSections K i).toRingHom)
  let g := (sourceCover K i).2.fromSpec
  letI : IsIso f := chartSpec_isIso K i
  letI : IsOpenImmersion g := (sourceCover K i).2.isOpenImmersion_fromSpec
  change (f ≫ g).opensRange = (sourceCover K i).1
  exact (Scheme.Hom.opensRange_comp_of_isIso f g).trans (sourceCover K i).2.opensRange_fromSpec

include aK hTower in
/-- The chart isomorphism preserves the specified polynomial map to
the actual base chart, not just the isomorphism class of its ring. -/
@[reassoc] theorem chart_over_base (i : Fin 2) :
    letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
    chartEmbedding K i ≫ modelMap K =
      Spec.algebraMap ℚ[X] (Order K i) ≫ JLineAtlas318.chart ℚ i := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  let e : Order K i ≃ₐ[ℚ[X]] Order K i := AlgEquiv.refl
  have h := NormalizationBaseCompatibility318.factored_chart_over_base
    (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℚ i)
    (genericMap K) (genericMap_factor K i) e
  have hr : ((actualSections K i).trans e.toRingEquiv).toRingHom =
      (actualSections K i).toRingHom := by apply RingHom.ext; intro x; rfl
  unfold chartEmbedding
  rw [← hr]
  exact h

/-- This is the unique affine iso with the stated embedding into
the same whole normalization. -/
@[expose] def chartIso (i : Fin 2) :
    Spec (CommRingCat.of (Order K i)) ≅ (sourceCover K i).1.toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartEmbedding K i) (sourceCover K i).1.ι
    (by rw [← Scheme.Hom.coe_opensRange,chartEmbedding_range,Scheme.Opens.range_ι])

theorem chartIso_fac (i : Fin 2) :
    (chartIso K i).hom ≫ (sourceCover K i).1.ι = chartEmbedding K i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem chartIso_unique (i : Fin 2)
    (u : Spec (CommRingCat.of (Order K i)) ⟶ (sourceCover K i).1.toScheme)
    (h : u ≫ (sourceCover K i).1.ι = chartEmbedding K i) :
    u = (chartIso K i).hom :=
  (cancel_mono _).mp (h.trans (chartIso_fac K i).symm)

@[expose] def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

open MvPolynomial HomogeneousLocalization in
theorem target_other_preimage (i : Fin 2) :
    (JLineAtlas318.chart ℚ i)⁻¹ᵁ(targetCover (other i)).1 =
      PrimeSpectrum.basicOpen (Polynomial.X : ℚ[X]) := by
  fin_cases i
  · exact JLineOverlapOpen318.chart_zero_preimage_one
  · change JLineAtlas318.chart ℚ 1⁻¹ᵁ(JLineAtlas318.chart ℚ 0 ''ᵁ ⊤) = _
    rw [Scheme.Hom.image_top_eq_opensRange,JLineAtlas318.chart_range]
    unfold JLineAtlas318.chart
    rw [Scheme.Hom.comp_preimage]
    erw [Proj.awayι_preimage_basicOpen (𝒜 := ProjectiveJLine318.grading ℚ)
      (isHomogeneous_X ℚ (1 : Fin 2)) (by omega)
      (isHomogeneous_X ℚ (0 : Fin 2)) (by omega)]
    change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv ℚ 1)
      (Away.isLocalizationElem (isHomogeneous_X ℚ (1 : Fin 2)) (isHomogeneous_X ℚ (0 : Fin 2)))) = _
    have h : Away.isLocalizationElem (isHomogeneous_X ℚ (1 : Fin 2))
        (isHomogeneous_X ℚ (0 : Fin 2)) = (JLineAtlas318.chartEquiv ℚ 1).symm Polynomial.X := by
      rw [JLineAtlas318.chartEquiv_symm_X]
      simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate] <;> rfl
    rw [h,AlgEquiv.apply_symm_apply]

include aK hTower in
theorem chart_overlap_preimage (i : Fin 2) :
    (chartEmbedding K i)⁻¹ᵁ(sourceCover K (other i)).1 =
      PrimeSpectrum.basicOpen (parameter K i) := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  change (chartEmbedding K i)⁻¹ᵁ((modelMap K)⁻¹ᵁ(targetCover (other i)).1) = _
  rw [← Scheme.Hom.comp_preimage,chart_over_base K i,Scheme.Hom.comp_preimage,
    target_other_preimage,SpecMap_preimage_basicOpen] <;> rfl

/-- The literal principal localization in the actual chart, as a
morphism into the very same global projective normalization. -/
@[expose] def overlapEmbedding (i : Fin 2) :
    Spec (CommRingCat.of (Localization.Away (parameter K i))) ⟶ model K :=
  Spec.algebraMap (Order K i) (Localization.Away (parameter K i)) ≫ chartEmbedding K i

instance (i : Fin 2) : IsOpenImmersion (overlapEmbedding K i) := by
  unfold overlapEmbedding
  letI : IsOpenImmersion (Spec.algebraMap (Order K i) (Localization.Away (parameter K i))) :=
    IsOpenImmersion.of_isLocalization (parameter K i)
  infer_instance

include aK hTower in
theorem overlap_range (i : Fin 2) :
    (overlapEmbedding K i).opensRange = (sourceCover K i).1 ⊓ (sourceCover K (other i)).1 := by
  unfold overlapEmbedding
  have hloc : (Spec.algebraMap (Order K i) (Localization.Away (parameter K i))).opensRange =
      PrimeSpectrum.basicOpen (parameter K i) := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  rw [Scheme.Hom.opensRange_comp,hloc,← chart_overlap_preimage K i,
    Scheme.Hom.image_preimage_eq_opensRange_inf,chartEmbedding_range]

include aK hTower in
/-- The actual scheme overlap iso is uniquely characterized by its
two chart embeddings into this same normalization (not by degree). -/
@[expose] def actualOverlapIso :
    Spec (CommRingCat.of (Localization.Away (parameter K 0))) ≅
      Spec (CommRingCat.of (Localization.Away (parameter K 1))) :=
  IsOpenImmersion.isoOfRangeEq (overlapEmbedding K 0) (overlapEmbedding K 1) (by
    rw [← Scheme.Hom.coe_opensRange,← Scheme.Hom.coe_opensRange,overlap_range,overlap_range]
    simp [other,inf_comm])

include aK hTower in
theorem actualOverlapIso_fac :
    (actualOverlapIso K).hom ≫ overlapEmbedding K 1 = overlapEmbedding K 0 :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end SelectedOriginalGenericCompactCharts318

#print axioms SelectedOriginalGenericCompactCharts318.chart_over_base
#print axioms SelectedOriginalGenericCompactCharts318.chartIso_unique
#print axioms SelectedOriginalGenericCompactCharts318.actualOverlapIso_fac
