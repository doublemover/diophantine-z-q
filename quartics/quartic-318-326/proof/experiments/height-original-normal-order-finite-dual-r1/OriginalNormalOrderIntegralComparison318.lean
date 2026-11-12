module
public import OriginalNormalOrderSameCenter318
public import OriginalNormalCenterAffineChart318
public import LocalSectionCotangentImageTransport318
public section
noncomputable section
namespace OriginalNormalOrderIntegralComparison318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
abbrev oldChart := OriginalNormalCenterAffineChart318.chart c t w D M
abbrev orderChart := OriginalNormalOrderSameCenter318.sectionChart c t w D M ht

/-- Both charts contain exactly the SAME whole M.center. The common
chart retains actual integral evaluations, not only generic agreement. -/
@[expose] def common := LocalSectionCommonChart318.common
  (oldChart c t w D M) (orderChart c t w D M ht)

@[expose] def integralComparison :
    OriginalNormalCenterAffineChart318.Cotangent c t w D M ≃ₗ[V c t w]
      OriginalNormalOrderSameCenter318.Cotangent c t w D M ht :=
  LocalSectionCotangentComparison318.comparison
    (oldChart c t w D M) (orderChart c t w D M ht) (common c t w D M ht)

/-- A differential comparison on the entire integral cotangent module
is constructed before scalar extension to the original signed-point field. -/
theorem integralComparison_differential
    (a : (oldChart c t w D M).ring) (b : (orderChart c t w D M ht).ring)
    (h : (common c t w D M ht).left.hom a = (common c t w D M ht).right.hom b) :
    integralComparison c t w D M ht (AffineSectionCotangentImage318.differential
      (oldChart c t w D M) a) = AffineSectionCotangentImage318.differential
        (orderChart c t w D M ht) b :=
  LocalSectionCotangentComparison318.comparison_differential _ _ _ a b h

@[expose] def genericComparison :
    OriginalNormalCenterAffineChart318.GenericCotangent c t w D M ≃ₗ[K c t]
      OriginalNormalOrderSameCenter318.GenericCotangent c t w D M ht :=
  LocalSectionCotangentImageTransport318.generic
    (oldChart c t w D M) (orderChart c t w D M ht) (K c t)
    (integralComparison c t w D M ht)

/-- The OLD center integral image is transported exactly onto the
normal-order chart integral image at the original point. This does not yet
identify the two independently constructed dt-coordinate maps. -/
theorem image_iff (x : OriginalNormalCenterAffineChart318.GenericCotangent c t w D M) :
    x ∈ OriginalNormalCenterAffineChart318.integralImage c t w D M ↔
    genericComparison c t w D M ht x ∈ AffineSectionCotangentImage318.integralImage
      (orderChart c t w D M ht) (K c t) :=
  LocalSectionCotangentImageTransport318.image_iff _ _ _ _ x
end OriginalNormalOrderIntegralComparison318
