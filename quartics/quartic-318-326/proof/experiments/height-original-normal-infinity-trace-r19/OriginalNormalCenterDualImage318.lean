module
public import OriginalNormalCenterPrincipalImage318
public import FinitePlaceMultiplicativeDual318
public section
noncomputable section
namespace OriginalNormalCenterDualImage318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318 OriginalNormalCenterCoordinateLattice318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "L" => scalarLattice c t w D M
local notation "a" => OriginalNormalCenterPrincipalImage318.generator c t w D M

/-- The actual full integral multiplicative dual of the closed-center
image in the SAME normalized-source coordinate, at every finite place. -/
@[expose] def dual : Submodule (V c t w) (K c t) :=
  FinitePlaceMultiplicativeDual318.dual w L

/-- Every actual integral cotangent is tested; this is not a condition
on a separately supplied frame or on a chosen pair of global sections. -/
lemma mem_iff (z : K c t) : z ∈ dual c t w D M ↔
    ∀ x : Cotangent c t w D M, w (coordinateMap c t w D M x*z) ≤ 1 := by
  rw [dual,FinitePlaceMultiplicativeDual318.mem_iff]
  constructor
  · intro hz x
    exact (FinitePlaceMultiplicativeDual318.mem_unit_iff w _).mp (hz _ ⟨x,rfl⟩)
  · intro hz y hy
    obtain ⟨x,rfl⟩ := hy
    exact (FinitePlaceMultiplicativeDual318.mem_unit_iff w _).mpr (hz x)

lemma dual_eq : dual c t w D M = FinitePlacePrincipalLattice318.lattice w a⁻¹ := by
  rw [dual,OriginalNormalCenterPrincipalImage318.lattice_eq,
    FinitePlaceMultiplicativeDual318.dual_principal w a
      (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M)]

lemma mem_iff_norm (z : K c t) : z ∈ dual c t w D M ↔ w z*w a ≤ 1 := by
  rw [dual_eq,FinitePlacePrincipalLattice318.mem_iff_norm w a⁻¹
    (inv_ne_zero (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M))]
  simp only [map_inv₀,inv_inv]

@[expose] def basis : V c t w ≃ₗ[V c t w] dual c t w D M := by
  rw [dual_eq]
  exact FinitePlacePrincipalLattice318.basis w a⁻¹
    (inv_ne_zero (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M))

lemma bidual_eq : FinitePlaceMultiplicativeDual318.dual w (dual c t w D M)=L :=
  FinitePlaceMultiplicativeDual318.bidual w L (scalarLattice_ne_bot c t w D M)

/-- Actual integral pairing on the whole original cotangent module,
with precisely its constructed source-frame coefficient. Torsion is
allowed; no Hodge/dualizing identification is inferred. -/
@[expose] def pairing (z : dual c t w D M) (x : Cotangent c t w D M) : V c t w :=
  FinitePlaceMultiplicativeDual318.pairing w L z ⟨coordinateMap c t w D M x,⟨x,rfl⟩⟩
lemma pairing_value (z : dual c t w D M) (x : Cotangent c t w D M) :
    algebraMap (V c t w) (K c t) (pairing c t w D M z x)=coordinateMap c t w D M x*z.val := rfl

/-- The chosen integral-image generator and its actual dual generator
have product one in the original point field. -/
lemma generator_pairing : a*a⁻¹=(1:K c t) :=
  mul_inv_cancel₀ (OriginalNormalCenterPrincipalImage318.generator_ne c t w D M)
end OriginalNormalCenterDualImage318
