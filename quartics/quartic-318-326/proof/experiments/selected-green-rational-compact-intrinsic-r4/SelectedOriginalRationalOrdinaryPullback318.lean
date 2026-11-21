module
public import SelectedOriginalRationalOrdinaryGeometry318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open SelectedOriginalGenericChartClosures318 SelectedRationalGenericFromComplex318
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryIntegral318 SelectedOriginalRationalOrdinaryOpening318
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryGeometry318

namespace SelectedOriginalRationalOrdinaryPullback318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hf : IsField (genericRoot N p))
variable (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))

/-- Exact agreement on all polynomial functions of the printed J,
not merely on their generic images in unrelated field copies. -/
theorem openingIso_polynomial (a : ℚ[X]) :
    openingIso N p hf hp hd
      (algebraMap (CompactOrder N p hf) (Localized N p hf)
        (algebraMap ℚ[X] (CompactOrder N p hf) a)) =
      algebraMap Base (ordinaryRoot N p) (algebraMap ℚ[X] Base a) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : IsScalarTower ℚ[X] Base QJ := rattower
  letI : Algebra (ordinaryRoot N p) (genericRoot N p) := (genericEmbedding N p).toAlgebra
  letI : IsIntegralClosure (ordinaryRoot N p) Base (genericRoot N p) :=
    actual_integralClosure N p hp hd
  have hj : Function.Injective (genericEmbedding N p) :=
    IsIntegralClosure.algebraMap_injective (ordinaryRoot N p) Base (genericRoot N p)
  apply hj
  rw [openingIso_order_value]
  change algebraMap QJ (genericRoot N p) (basePolynomial 1 a) =
    tensorComparison N p
      (algebraMap (ordinaryRoot N p) (Tensor N p)
        (algebraMap Base (ordinaryRoot N p) (algebraMap ℚ[X] Base a)))
  rw [← IsScalarTower.algebraMap_apply Base (ordinaryRoot N p) (Tensor N p),AlgEquiv.commutes]
  change algebraMap QJ (genericRoot N p) (basePolynomial 1 a) =
    algebraMap QJ (genericRoot N p) (algebraMap Base QJ (algebraMap ℚ[X] Base a))
  rw [← IsScalarTower.algebraMap_apply ℚ[X] Base QJ]
  simp [basePolynomial]

@[expose] def baseEmbedding :
    Spec (CommRingCat.of Base) ⟶ ProjectiveJLine318.scheme ℚ :=
  Spec.algebraMap ℚ[X] Base ≫ JLineAtlas318.chart ℚ 1

instance baseEmbedding_open : IsOpenImmersion baseEmbedding := by
  unfold baseEmbedding
  letI : IsOpenImmersion (Spec.algebraMap ℚ[X] Base) :=
    IsOpenImmersion.of_isLocalization denominator
  infer_instance

theorem baseEmbedding_range : baseEmbedding.opensRange = baseOrdinary := by
  have hloc : (Spec.algebraMap ℚ[X] Base).opensRange = PrimeSpectrum.basicOpen denominator := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  rw [baseEmbedding,Scheme.Hom.opensRange_comp,hloc,baseOrdinary]

/-- The projection of the reconstructed ordinary source is the
original J-line projection, as equality of global scheme morphisms. -/
theorem ordinary_over_J :
    ordinaryEmbedding N p hf hp hd ≫ compactJ N p hf =
      Spec.algebraMap Base (ordinaryRoot N p) ≫ baseEmbedding := by
  simp only [ordinaryEmbedding,Category.assoc,chart_over_J,baseEmbedding]
  change Spec.map (CommRingCat.ofHom (openingIso N p hf hp hd).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CompactOrder N p hf) (Localized N p hf))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] (CompactOrder N p hf))) ≫
      JLineAtlas318.chart ℚ 1 =
    Spec.map (CommRingCat.ofHom (algebraMap Base (ordinaryRoot N p))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] Base)) ≫ JLineAtlas318.chart ℚ 1
  simp only [← Spec.map_comp_assoc]
  have h :
      CommRingCat.ofHom (algebraMap ℚ[X] (CompactOrder N p hf)) ≫
        (CommRingCat.ofHom (algebraMap (CompactOrder N p hf) (Localized N p hf)) ≫
          CommRingCat.ofHom (openingIso N p hf hp hd).toRingHom) =
      CommRingCat.ofHom (algebraMap ℚ[X] Base) ≫
        CommRingCat.ofHom (algebraMap Base (ordinaryRoot N p)) :=
    CommRingCat.hom_ext (openingIso_polynomial N p hf hp hd)
  rw [h]

/-- Not just an isomorphic open: it is the full cartesian base change
of the normalization projection along the exact ordinary J-chart. -/
theorem ordinary_pullback :
    IsPullback (Spec.algebraMap Base (ordinaryRoot N p)) (ordinaryEmbedding N p hf hp hd)
      baseEmbedding (compactJ N p hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (ordinary_over_J N p hf hp hd) (by
    rw [baseEmbedding_range,ordinaryEmbedding_range] <;> rfl)

end SelectedOriginalRationalOrdinaryPullback318

#print axioms SelectedOriginalRationalOrdinaryPullback318.ordinary_over_J
#print axioms SelectedOriginalRationalOrdinaryPullback318.ordinary_pullback
