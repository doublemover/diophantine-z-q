module
public import SelectedOriginalRationalOrdinaryOpening318
public import SelectedRationalRootCompactInstall318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericCompactNormal318
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryIntegral318 SelectedOriginalRationalOrdinaryOpening318
open SelectedRationalRootCompactInstall318

namespace SelectedOriginalRationalOrdinaryGeometry318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hf : IsField (genericRoot N p))

/-- The genuine open of the original projective base: the affine j
chart with the original elliptic values 0 and 1728 removed. -/
@[expose] def baseOrdinary : (ProjectiveJLine318.scheme ℚ).Opens :=
  JLineAtlas318.chart ℚ 1 ''ᵁ PrimeSpectrum.basicOpen denominator

abbrev actualOpen : (compact N p hf).Opens := (compactJ N p hf)⁻¹ᵁ baseOrdinary

@[expose] def chart :
    Spec (CommRingCat.of (CompactOrder N p hf)) ⟶ compact N p hf := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ (genericRoot N p) := rationalAlgebra N p
  letI : IsScalarTower ℚ JField (genericRoot N p) := rationalTower N p
  exact SelectedOriginalGenericCompactCharts318.chartEmbedding (genericRoot N p) 1

instance chart_open : IsOpenImmersion (chart N p hf) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ (genericRoot N p) := rationalAlgebra N p
  letI : IsScalarTower ℚ JField (genericRoot N p) := rationalTower N p
  unfold chart
  infer_instance

theorem chart_range :
    (chart N p hf).opensRange = (compactJ N p hf)⁻¹ᵁ(targetCover 1).1 := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ (genericRoot N p) := rationalAlgebra N p
  letI : IsScalarTower ℚ JField (genericRoot N p) := rationalTower N p
  exact SelectedOriginalGenericCompactCharts318.chartEmbedding_range (genericRoot N p) 1

theorem chart_over_J :
    chart N p hf ≫ compactJ N p hf =
      Spec.algebraMap ℚ[X] (CompactOrder N p hf) ≫ JLineAtlas318.chart ℚ 1 := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ (genericRoot N p) := rationalAlgebra N p
  letI : IsScalarTower ℚ JField (genericRoot N p) := rationalTower N p
  exact SelectedOriginalGenericCompactCharts318.chart_over_base (genericRoot N p) 1

theorem chart_ordinary_preimage :
    (chart N p hf)⁻¹ᵁ(actualOpen N p hf) =
      PrimeSpectrum.basicOpen (openParameter N p hf) := by
  change (chart N p hf)⁻¹ᵁ((compactJ N p hf)⁻¹ᵁ baseOrdinary) = _
  rw [← Scheme.Hom.comp_preimage,chart_over_J,Scheme.Hom.comp_preimage,
    baseOrdinary,Scheme.Hom.preimage_image_eq,SpecMap_preimage_basicOpen] <;> rfl

abbrev Localized := Localization.Away (openParameter N p hf)

@[expose] def localizeMap :
    Spec (CommRingCat.of (Localized N p hf)) ⟶ Spec (CommRingCat.of (CompactOrder N p hf)) :=
  Spec.algebraMap (CompactOrder N p hf) (Localized N p hf)

instance localizeMap_open : IsOpenImmersion (localizeMap N p hf) :=
  IsOpenImmersion.of_isLocalization (openParameter N p hf)

theorem localizeMap_range :
    (localizeMap N p hf).opensRange = PrimeSpectrum.basicOpen (openParameter N p hf) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range _ _

variable (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))

@[expose] def rootMap :
    Spec (CommRingCat.of (ordinaryRoot N p)) ⟶ Spec (CommRingCat.of (Localized N p hf)) :=
  Spec.map (CommRingCat.ofHom (openingIso N p hf hp hd).toRingHom)

instance rootMap_isIso : IsIso (rootMap N p hf hp hd) := by
  change IsIso (Spec.map (openingIso N p hf hp hd).toCommRingCatIso.hom)
  infer_instance

/-- Actual immersion of the whole rational ordinary root algebra into
the whole compact model, defined by the exact localization isomorphism. -/
@[expose] def ordinaryEmbedding :
    Spec (CommRingCat.of (ordinaryRoot N p)) ⟶ compact N p hf :=
  rootMap N p hf hp hd ≫ localizeMap N p hf ≫ chart N p hf

instance ordinaryEmbedding_open : IsOpenImmersion (ordinaryEmbedding N p hf hp hd) := by
  unfold ordinaryEmbedding
  infer_instance

theorem ordinaryEmbedding_range :
    (ordinaryEmbedding N p hf hp hd).opensRange = actualOpen N p hf := by
  have hle : actualOpen N p hf ≤ (compactJ N p hf)⁻¹ᵁ(targetCover 1).1 :=
    (compactJ N p hf).preimage_mono ((JLineAtlas318.chart ℚ 1).image_mono le_top)
  unfold ordinaryEmbedding
  rw [Scheme.Hom.opensRange_comp_of_isIso,Scheme.Hom.opensRange_comp,localizeMap_range,
    ← chart_ordinary_preimage,Scheme.Hom.image_preimage_eq_opensRange_inf,
    chart_range,inf_eq_right.mpr hle]

/-- The requested genuine preimage open, not just an abstract ring of
the same degree, with unique factorization into the actual compact curve. -/
def ordinaryIso :
    Spec (CommRingCat.of (ordinaryRoot N p)) ≅ (actualOpen N p hf).toScheme :=
  IsOpenImmersion.isoOfRangeEq (ordinaryEmbedding N p hf hp hd) (actualOpen N p hf).ι
    (by rw [← Scheme.Hom.coe_opensRange,ordinaryEmbedding_range,Scheme.Opens.range_ι])

theorem ordinaryIso_fac :
    (ordinaryIso N p hf hp hd).hom ≫ (actualOpen N p hf).ι =
      ordinaryEmbedding N p hf hp hd :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- This ordinary embedding has the very SAME generic point, not
merely a finite map of the same degree over an abstract projective line. -/
theorem ordinary_original :
    letI : Field (genericRoot N p) := hf.toField
    Spec.map (CommRingCat.ofHom (genericEmbedding N p)) ≫ ordinaryEmbedding N p hf hp hd =
      (genericMap (genericRoot N p)).toNormalization := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ (genericRoot N p) := rationalAlgebra N p
  letI : IsScalarTower ℚ JField (genericRoot N p) := rationalTower N p
  change Spec.map (CommRingCat.ofHom (genericEmbedding N p)) ≫
      (rootMap N p hf hp hd ≫ localizeMap N p hf ≫ chart N p hf) =
        (genericMap (genericRoot N p)).toNormalization
  unfold rootMap localizeMap
  rw [← Category.assoc,← Spec.map_comp,← Category.assoc,← Spec.map_comp]
  have h :
      CommRingCat.ofHom (algebraMap (CompactOrder N p hf) (Localized N p hf)) ≫
      (CommRingCat.ofHom (openingIso N p hf hp hd).toRingHom ≫
        CommRingCat.ofHom (genericEmbedding N p)) =
        CommRingCat.ofHom (SelectedOriginalCompactOverlapIdentity318.orderVal (genericRoot N p) 1) :=
    CommRingCat.hom_ext (openingIso_order_value N p hf hp hd)
  rw [h]
  exact SelectedOriginalCompactOverlapIdentity318.chart_original (genericRoot N p) 1

end SelectedOriginalRationalOrdinaryGeometry318

#print axioms SelectedOriginalRationalOrdinaryGeometry318.ordinaryIso_fac
#print axioms SelectedOriginalRationalOrdinaryGeometry318.ordinary_original
