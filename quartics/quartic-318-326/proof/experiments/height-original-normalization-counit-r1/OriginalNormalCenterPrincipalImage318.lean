module
public import OriginalNormalCenterCoordinateLattice318
public import FinitePlaceFiniteLatticeGenerator318
public section
noncomputable section
namespace OriginalNormalCenterPrincipalImage318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318 OriginalNormalCenterCoordinateLattice318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "L" => scalarLattice c t w D M

/-- A produced nonzero generator of the ACTUAL whole-center coefficient
image, on the SAME normal model and normalized-source dt coordinate. -/
@[expose] def generator : K c t :=
  FinitePlaceFiniteLatticeGenerator318.generator w L (scalarLattice_ne_bot c t w D M)
lemma generator_ne : generator c t w D M ≠ 0 :=
  FinitePlaceFiniteLatticeGenerator318.generator_ne w L (scalarLattice_ne_bot c t w D M)
lemma generator_mem : generator c t w D M ∈ L :=
  FinitePlaceFiniteLatticeGenerator318.generator_mem w L (scalarLattice_ne_bot c t w D M)
lemma lattice_eq : L = FinitePlacePrincipalLattice318.lattice w (generator c t w D M) :=
  FinitePlaceFiniteLatticeGenerator318.generator_lattice w L (scalarLattice_ne_bot c t w D M)

/-- This generator is the coordinate of a genuine integral cotangent
specialization, not merely an arbitrary point of the generic line. -/
lemma generator_is_integral_image :
    ∃ x : Cotangent c t w D M, coordinateMap c t w D M x=generator c t w D M :=
  generator_mem c t w D M

/-- An explicit integral rank-one frame of the ACTUAL embedded image.
This does not make the original possibly torsion cotangent module free. -/
@[expose] def basis : V c t w ≃ₗ[V c t w] L := by
  rw [lattice_eq]
  exact FinitePlacePrincipalLattice318.basis w (generator c t w D M) (generator_ne c t w D M)

lemma mem_iff_norm (x : K c t) :
    x ∈ L ↔ w x * (w (generator c t w D M))⁻¹ ≤ 1 := by
  rw [lattice_eq]
  exact FinitePlacePrincipalLattice318.mem_iff_norm w _ (generator_ne c t w D M) x

/-- The exact radius is intrinsic to this image even though its chosen
generator need not be canonical. No numerical valuation is asserted. -/
lemma generator_radius_unique (a : K c t) (ha : a ≠ 0)
    (he : L=FinitePlacePrincipalLattice318.lattice w a) :
    w a=w (generator c t w D M) :=
  FinitePlaceFiniteLatticeGenerator318.generator_norm_unique w L a
    (generator c t w D M) ha (generator_ne c t w D M) he (lattice_eq c t w D M)

/-- Exact membership of the same normalized-source dt in the integral
image. Its integrality is characterized, NOT assumed or concluded. -/
lemma source_dt_mem_iff :
    OriginalNormalSourceCotangent318.dt c t w D M ∈ sourceLattice c t w D M ↔
      (w (generator c t w D M))⁻¹ ≤ 1 := by
  have he : OriginalNormalSourceCotangent318.dt c t w D M ∈ sourceLattice c t w D M ↔
      (1:K c t) ∈ L := by
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨x,?_⟩
      rw [coordinateMap_through_source,LinearMap.comp_apply,hx,
        OriginalNormalSourceCotangent318.frame_dt]
    · rintro ⟨x,hx⟩
      refine ⟨x,?_⟩
      apply (OriginalNormalSourceCotangent318.frame c t w D M).injective
      rw [OriginalNormalSourceCotangent318.frame_dt]
      change coordinateMap c t w D M x=1 at hx
      rw [coordinateMap_through_source,LinearMap.comp_apply] at hx
      exact hx
  rw [he,mem_iff_norm]
  simp only [map_one,one_mul]
end OriginalNormalCenterPrincipalImage318
