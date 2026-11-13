module
public import OriginalNormalTwoChartCover318
public import IntegralJLineOverlapOpen318
public import OriginalNormalOverlapNativeComparison318
public section
noncomputable section
namespace OriginalNormalFullOverlap318
open NumberField Polynomial AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "B" => SourceOpenRing c t w D
local notation "Ni" => OriginalNormalInfinityOrder318.Order c t w D
local notation "Oi" => IntegralOriginalNormalOverlap318.InfinityOverlap R a d
local notation "f" => OriginalNormalOrderChart318.chart c t w D M
local notation "g" => OriginalNormalInfinityChart318.chart c t w D M
local notation "j" => NormalOverlapReciprocalDualSheaf318.map R a d
local notation "i" => IntegralNormalFiniteDualSheafRestriction318.map R a d
local notation "k" => IntegralNormalInfinityDualSheafRestriction318.map R a d
local instance sourceDomain : IsDomain B :=
  IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)

/-- Exact image of the old normal-order principal-localization map,
with the reciprocal polynomial scalar action retained. -/
lemma infinity_localization_range : k.opensRange=
    PrimeSpectrum.basicOpen (OriginalNormalInfinityOrder318.polynomialScalar c t w D X) := by
  letI := OriginalNormalOverlapOrderLocalization318.infinityNormalAlgebra R a d
  letI := OriginalNormalOverlapOrderLocalization318.infinity_localization R a d
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range Oi
    (OriginalNormalInfinityOrder318.polynomialScalar c t w D X)

/-- Pulling back the full finite chart along the actual infinity chart
is exactly the whole reciprocal normal localization, not the unbranched
source and not merely a generic-point equality. -/
lemma infinity_preimage_finite : g ⁻¹ᵁ f.opensRange=k.opensRange := by
  rw [OriginalNormalChartRanges318.finite_range,←Scheme.Hom.comp_preimage,
    OriginalNormalInfinityChart318.base,Scheme.Hom.comp_preimage,
    IntegralJLineOverlapOpen318.zero_one,infinity_localization_range]
  rfl

/-- The accepted reciprocal overlap and the OLD localization maps form
the categorical intersection of the two entire normal-order charts. -/
theorem actual_pullback : IsPullback (j ≫ i) k f g := by
  apply IsOpenImmersion.isPullback
  · simpa only [Category.assoc] using
      (OriginalNormalOverlapChartEquality318.square c t w D M).symm
  · exact infinity_preimage_finite c t w D M

/-- Full intersection of the images inside the original M. -/
theorem full_intersection : f.opensRange ⊓ g.opensRange=
    (OriginalNormalOverlapChartMaps318.infinity c t w D M).opensRange := by
  rw [inf_comm,←Scheme.Hom.image_preimage_eq_opensRange_inf,
    infinity_preimage_finite,←Scheme.Hom.opensRange_comp]
  rfl

/-- The existing native comparison is therefore on the actual full
intersection. This does NOT identify it with a global dualizing object. -/
theorem comparison_domain : g ⁻¹ᵁ f.opensRange=k.opensRange :=
  infinity_preimage_finite c t w D M
end OriginalNormalFullOverlap318
