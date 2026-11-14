module
public import OriginalNormalizationDifferentValue318
public section
noncomputable section
namespace OriginalNormalizationConductorSpecialization318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalizationDifferentValue318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "B" => SourceOpenRing c t w D
local notation "a" => contacts c t w
local notation "δ" => differentValue c t w D M

/-- Actual field values of the normalization conductor and trace
codifferent, under the SAME original signed point map. They are not
asserted finite V-lattices when the point does not lie on the finite chart. -/
@[expose] def conductorValues : Submodule R (K c t) :=
  ((IntegralFourRootNormalizationConductor318.conductor R a D.coefficients).restrictScalars R).map
    (evaluation c t w D M).toLinearMap
@[expose] def codifferentValues : Submodule R (K c t) :=
  ((IntegralFourRootNormalizationConductor318.codifferent R a D.coefficients).restrictScalars R).map
    (evaluation c t w D M).toLinearMap

/-- Exact inverse-different conductor correction AFTER specialization
at the original signed point, still as actual subsets of its original field. -/
lemma mem_iff_inverse (z : K c t) : z ∈ codifferentValues c t w D M ↔
    ∃ y : K c t,y ∈ conductorValues c t w D M ∧ z=δ⁻¹*y := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := (IntegralFourRootNormalizationConductor318.mem_codifferent_iff_inverse
      R a D.coefficients x).mp hx
    refine ⟨evaluation c t w D M y,⟨y,hy,rfl⟩,?_⟩
    change evaluation c t w D M x=_
    rw [hxy,map_mul,inverse_different_value]
  · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
    let u := (IntegralFourRootNormalizationConductor318.different_isUnit R a D.coefficients).unit
    refine ⟨(↑u⁻¹ : B)*x,?_,?_⟩
    · exact (IntegralFourRootNormalizationConductor318.mem_codifferent_iff_inverse
        R a D.coefficients _).mpr ⟨x,hx,rfl⟩
    · change evaluation c t w D M ((↑u⁻¹ : B)*x)=_
      rw [map_mul,inverse_different_value]

lemma mem_iff_conductor (z : K c t) : z ∈ codifferentValues c t w D M ↔
    δ*z ∈ conductorValues c t w D M := by
  rw [mem_iff_inverse]
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [←mul_assoc,mul_inv_cancel₀ (differentValue_ne c t w D M),one_mul] using hy
  · intro hz
    refine ⟨δ*z,hz,?_⟩
    rw [←mul_assoc,inv_mul_cancel₀ (differentValue_ne c t w D M),one_mul]

/-- Precise remaining comparison with the actual closed-center
cotangent IMAGE. This equivalence isolates the needed
conductor specialization statement; it DOES NOT assert that statement
or identify either object with a geometric Hodge/dualizing lattice. -/
theorem cotangent_comparison_iff :
    codifferentValues c t w D M=OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M ↔
    ∀ z : K c t,z ∈ OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M ↔
      δ*z ∈ conductorValues c t w D M := by
  constructor
  · intro h z
    rw [←h]
    exact mem_iff_conductor c t w D M z
  · intro h
    apply Submodule.ext
    intro z
    exact (mem_iff_conductor c t w D M z).trans (h z).symm
/-- Pairing with the ACTUAL cotangent dual detects the original image.
The codifferent is a candidate differential coefficient module, not a
candidate tangent-dual module; these two roles are kept distinct. -/
lemma integral_pairing_iff (z : K c t) :
    (∀ q ∈ OriginalNormalCenterDualImage318.dual c t w D M,w (q*z) ≤ 1) ↔
      z ∈ OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M := by
  rw [←OriginalNormalCenterDualImage318.bidual_eq c t w D M,
    FinitePlaceMultiplicativeDual318.mem_iff]
  simp only [FinitePlaceMultiplicativeDual318.mem_unit_iff]

/-- The remaining discrepancy is a concrete integral-pairing test.
Neither this inclusion nor equality with canonical/Hodge sections is assumed. -/
lemma codifferent_pairs_integrally_iff :
    (∀ z ∈ codifferentValues c t w D M,
      ∀ q ∈ OriginalNormalCenterDualImage318.dual c t w D M,w (q*z) ≤ 1) ↔
    codifferentValues c t w D M ≤
      OriginalNormalCenterCoordinateLattice318.scalarLattice c t w D M := by
  constructor
  · intro h z hz
    exact (integral_pairing_iff c t w D M z).mp (h z hz)
  · intro h z hz
    exact (integral_pairing_iff c t w D M z).mpr (h hz)
end OriginalNormalizationConductorSpecialization318
