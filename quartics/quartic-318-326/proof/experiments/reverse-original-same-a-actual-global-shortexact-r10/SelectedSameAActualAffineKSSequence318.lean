module

public import SelectedSameACechEpsilonReadout318
import all SelectedSameACechEpsilonReadout318
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual affine directional sequence with the marked d-epsilon

The two maps are the indicated d-epsilon injection and the native
Kähler fibre map. The proof of exactness uses the actual principal
closed-fibre kernel, not a prescribed split extension.
-/

public section

open scoped TensorProduct

namespace SelectedSameAActualAffineKSSequence318

open SelectedSameADualNumberFlatCoefficient318
open SelectedSameAADualNumberAffineChart318
open SelectedSameACechEpsilonReadout318

variable (k C B : Type*) [CommRing k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B] [Algebra (TrivSqZeroExt k k) C]
  [Algebra C B] [IsScalarTower k C B]

abbrev E := B ⊗[C] Ω[C⁄k]

/-- The actual first parameter's differential, not an independent frame choice. -/
noncomputable def dEps : E k C B :=
  (1 : B) ⊗ₜ[C] KaehlerDifferential.D k C (epsilonIn k C)

/-- The precise left map of the actual affine short sequence. -/
noncomputable def ι : B →ₗ[B] E k C B where
  toFun b := b • dEps k C B
  map_add' b c := add_smul b c (dEps k C B)
  map_smul' a b := by
    change (a * b) • dEps k C B = a • (b • dEps k C B)
    exact mul_smul a b _

noncomputable abbrev π : E k C B →ₗ[B] Ω[B⁄k] := KaehlerDifferential.mapBaseChange k C B

variable (hk : RingHom.ker (algebraMap C B) = Ideal.span ({epsilonIn k C} : Set C))

include hk in
private theorem map_epsilon : algebraMap C B (epsilonIn k C) = 0 := by
  apply RingHom.mem_ker.mp
  rw [hk]
  exact Ideal.mem_span_singleton_self _

include hk in
private theorem tensor_D_product (c : C) :
    (1 : B) ⊗ₜ[C] KaehlerDifferential.D k C (epsilonIn k C * c) =
      algebraMap C B c • dEps k C B := by
  have hz : epsilonIn k C • (1 : B) = 0 := by
    rw [← Algebra.algebraMap_eq_smul_one, map_epsilon k C B hk]
  have hc : c • (1 : B) = algebraMap C B c := (Algebra.algebraMap_eq_smul_one c).symm
  rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
    hz, TensorProduct.zero_tmul, zero_add, ← TensorProduct.smul_tmul, hc] <;>
    simp only [dEps, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

include hk in
/-- The actual right map has exactly the span of d-epsilon as its kernel,
over the genuine residue action, and is surjective. -/
theorem exact_at_middle (hSurj : Function.Surjective (algebraMap C B)) :
    Function.Surjective (π k C B) ∧ Function.Exact (ι k C B) (π k C B) := by
  refine ⟨KaehlerDifferential.mapBaseChange_surjective k C B hSurj, ?_⟩
  intro x
  constructor
  · intro hx
    have h := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k C B hSurj
    obtain ⟨v, hv⟩ := (h x).mp hx
    obtain ⟨z, rfl⟩ := Ideal.toCotangent_surjective _ v
    have hz : (z : C) ∈ Ideal.span ({epsilonIn k C} : Set C) := by
      rw [← hk]
      exact z.property
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨algebraMap C B c, ?_⟩
    change algebraMap C B c • dEps k C B = x
    rw [← tensor_D_product k C B hk c, ← hc]
    simpa only [KaehlerDifferential.kerCotangentToTensor_toCotangent] using hv
  · rintro ⟨b, rfl⟩
    change (π k C B) (b • dEps k C B) = 0
    unfold dEps
    rw [LinearMap.map_smul, KaehlerDifferential.mapBaseChange_tmul,
      KaehlerDifferential.map_D, map_epsilon k C B hk, map_zero] <;> simp only [smul_zero]

variable [hFlat : Module.Flat (TrivSqZeroExt k k) C]
variable (ρ : C →ₐ[k] B) (s : B →ₐ[k] C) (hs : ∀ a, ρ (s a) = a)
  (hρ : algebraMap C B = ρ.toRingHom)

include ρ s hs hk hρ hFlat in
/-- The true affine chart explicitly retracts the first differential.
This proves injectivity without requiring the closed-fibre map to be flat. -/
theorem epsilon_injective : Function.Injective (ι k C B) := by
  have hk' : RingHom.ker ρ.toRingHom = Ideal.span ({epsilonIn k C} : Set C) := by
    rw [← hρ, hk]
  let ν := coefficientDerivation k C B ρ s hs hk' hρ
  let r : E k C B →ₗ[B] B := ν.liftKaehlerDifferential.liftBaseChange B
  have hr : r (dEps k C B) = 1 := by
    change ν.liftKaehlerDifferential.liftBaseChange B
      ((1 : B) ⊗ₜ[C] KaehlerDifferential.D k C (epsilonIn k C)) = 1
    rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
    change coefficient k C B ρ s hs hk' (epsilonIn k C) = 1
    exact coefficient_on_epsilon k C B ρ s hs hk'
  have hleft : Function.LeftInverse r (ι k C B) := by
    intro b
    change r (b • dEps k C B) = b
    rw [LinearMap.map_smul, hr, smul_eq_mul, mul_one]
  exact hleft.injective

end SelectedSameAActualAffineKSSequence318
