module
public import OriginalCotangentPathCoherence318
public section
noncomputable section
namespace OriginalCotangentCoordinateTransfer318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)

/-- Equality of ACTUAL source paths transfers the exact original dt
coordinate map, not merely an abstract rank-one lattice isomorphism. -/
theorem coordinate_apply (x : OriginalNormalCenterAffineChart318.Cotangent c t w D M) :
    OriginalNormalCenterCoordinateLattice318.coordinateMap c t w D M x =
      OriginalNormalOrderCotangentCoordinate318.coordinateMap c t w D M ht
        (OriginalNormalOrderIntegralComparison318.integralComparison c t w D M ht x) := by
  have hp := congrArg (fun e => e
    (AffineSectionCotangentImage318.toGeneric
      (OriginalNormalCenterAffineChart318.chart c t w D M) (K c t) x))
    (OriginalCotangentPathCoherence318.comparison c t w D M ht)
  have hi := LocalSectionCotangentImageTransport318.generic_toGeneric
    (OriginalNormalCenterAffineChart318.chart c t w D M)
    (OriginalNormalOrderSameCenter318.sectionChart c t w D M ht) (K c t)
    (OriginalNormalOrderIntegralComparison318.integralComparison c t w D M ht) x
  change OriginalNormalSourceCotangent318.frame c t w D M
      (OriginalNormalCenterCommonChart318.genericComparison c t w D M
        (AffineSectionCotangentImage318.toGeneric
          (OriginalNormalCenterAffineChart318.chart c t w D M) (K c t) x)) =
    OriginalNormalSourceCotangent318.frame c t w D M
      (OriginalNormalOrderCotangentCoordinate318.genericComparison c t w D M ht
        (AffineSectionCotangentImage318.toGeneric
          (OriginalNormalOrderSameCenter318.sectionChart c t w D M ht) (K c t)
          (OriginalNormalOrderIntegralComparison318.integralComparison c t w D M ht x)))
  apply congrArg (OriginalNormalSourceCotangent318.frame c t w D M)
  exact hp.symm.trans (congrArg
    (OriginalNormalOrderCotangentCoordinate318.genericComparison c t w D M ht) hi)

/-- Equality of subsets in the SAME original field with the SAME dt
coordinate, rather than just an isomorphism of integral modules. -/
theorem image_eq : OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M =
    OriginalNormalOrderCotangentCoordinate318.image c t w D M ht := by
  ext z
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨OriginalNormalOrderIntegralComparison318.integralComparison c t w D M ht x,
      (coordinate_apply c t w D M ht x).symm.trans hx⟩
  · rintro ⟨y,hy⟩
    refine ⟨(OriginalNormalOrderIntegralComparison318.integralComparison c t w D M ht).symm y,?_⟩
    rw [coordinate_apply,LinearEquiv.apply_symm_apply]
    exact hy

include ht in
theorem one_mem : (1:K c t) ∈
    OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M := by
  rw [image_eq c t w D M ht]
  exact OriginalNormalOrderCotangentCoordinate318.one_mem c t w D M ht

include ht in
/-- The original source dt now lies in the OLD integral-center image.
Its preimage is produced by the integral comparison, not assumed. -/
theorem dt_mem : OriginalNormalCenterCoordinateLattice318.dt c t w D M ∈
    OriginalNormalCenterAffineChart318.integralImage c t w D M := by
  obtain ⟨x,hx⟩ := one_mem c t w D M ht
  refine ⟨x,?_⟩
  apply (OriginalNormalCenterCoordinateLattice318.frame c t w D M).injective
  change OriginalNormalCenterCoordinateLattice318.coordinateMap c t w D M x =
    OriginalNormalCenterCoordinateLattice318.frame c t w D M
      (OriginalNormalCenterCoordinateLattice318.dt c t w D M)
  rw [hx,OriginalNormalCenterCoordinateLattice318.frame_dt]

include ht in
/-- Bound on EVERY element of the full actual old-center
multiplicative dual, after the proved coordinate-path identification. -/
theorem dual_bound (q : K c t)
    (hq : q ∈ OriginalNormalCenterDualImage318.dual c t w D M) : w q ≤ 1 := by
  apply OriginalNormalOrderCotangentCoordinate318.dual_bound c t w D M ht q
  change q ∈ FinitePlaceMultiplicativeDual318.dual w
    (OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M) at hq
  rwa [image_eq c t w D M ht] at hq
end OriginalCotangentCoordinateTransfer318
