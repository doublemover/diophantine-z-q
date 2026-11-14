module
public import OriginalNormalizationFiniteImage318
public section
noncomputable section
namespace OriginalNormalizationCotangentDiscrepancy318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalizationConductorSpecialization318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
local notation "R" => V c t w
local notation "L" => codifferentValues c t w D M
local notation "H" => OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M
local notation "α" => OriginalNormalCenterPrincipalImage318.generator c t w D M
local instance : Module.Finite R L := OriginalNormalizationFiniteImage318.finite_codifferentValues c t w D M ht

/-- Produced from the ACTUAL normalized-codifferent image on the actual
integral finite-coordinate branch; not a supplied canonical/Hodge frame. -/
@[expose] def generator : K c t :=
  FinitePlaceFiniteLatticeGenerator318.generator w L
    (OriginalNormalizationConductorNonzero318.codifferentValues_ne_bot c t w D M)
lemma generator_ne : generator c t w D M ht ≠ 0 :=
  FinitePlaceFiniteLatticeGenerator318.generator_ne w L
    (OriginalNormalizationConductorNonzero318.codifferentValues_ne_bot c t w D M)
lemma image_eq : L=FinitePlacePrincipalLattice318.lattice w (generator c t w D M ht) :=
  FinitePlaceFiniteLatticeGenerator318.generator_lattice w L
    (OriginalNormalizationConductorNonzero318.codifferentValues_ne_bot c t w D M)

/-- A genuine ratio between two PRODUCED original-point images, both
in the same dt coordinate. It is not yet a regular-model discrepancy. -/
@[expose] def ratio : K c t := generator c t w D M ht / α
lemma ratio_ne : ratio c t w D M ht ≠ 0 :=
  div_ne_zero (generator_ne c t w D M ht)
    (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M)

/-- The missing containment is now exactly a bound on this actual
ratio, not an abstract dimension-one statement or an assumed equality. -/
lemma inclusion_iff : L ≤ H ↔ w (ratio c t w D M ht) ≤ 1 := by
  rw [ratio,map_div₀,div_eq_mul_inv]
  rw [←OriginalNormalCenterPrincipalImage318.mem_iff_norm c t w D M]
  rw [image_eq c t w D M ht]
  constructor
  · intro h
    apply h
    exact ⟨1,by
      change algebraMap R (K c t) 1 * generator c t w D M ht=generator c t w D M ht
      rw [map_one,one_mul]⟩
  · exact FinitePlacePrincipalLattice318.lattice_le_of_mem w _ H

lemma image_eq_iff_radius : L=H ↔ w (generator c t w D M ht)=w α := by
  constructor
  · intro h
    exact FinitePlaceFiniteLatticeGenerator318.generator_norm_unique w L
      (generator c t w D M ht) α (generator_ne c t w D M ht)
      (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M)
      (image_eq c t w D M ht) (h.trans (OriginalNormalCenterPrincipalImage318.lattice_eq c t w D M))
  · intro h
    rw [image_eq c t w D M ht,OriginalNormalCenterPrincipalImage318.lattice_eq]
    exact FinitePlacePrincipalLattice318.eq_of_norm w _ _ (generator_ne c t w D M ht)
      (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M) h

/-- Full integral pairing of normalized-codifferent values with the
actual center cotangent dual is exactly the same ratio bound. The bound
is not asserted, and no Hodge/dualizing identification is imported. -/
lemma pairing_iff :
    (∀ z ∈ L,∀ q ∈ OriginalNormalCenterDualImage318.dual c t w D M,w (q*z) ≤ 1) ↔
      w (ratio c t w D M ht) ≤ 1 :=
  (codifferent_pairs_integrally_iff c t w D M).trans (inclusion_iff c t w D M ht)
end OriginalNormalizationCotangentDiscrepancy318
