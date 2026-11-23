module
public import SelectedJIntegralScaledTraceDual318
public import SelectedJTraceDualCoefficients318
public import SelectedJTraceDiagonalDerivation318
import all SelectedJIntegralScaledTraceDual318

public section
noncomputable section

namespace SelectedJDifferentAnnihilates318

open Algebra Module
open SelectedJIntegralScaledTraceDual318 SelectedJTraceDualCoefficients318
open scoped TensorProduct nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
  [IsIntegralClosure B A (FractionRing B)]
  [FiniteDimensional (FractionRing A) (FractionRing B)]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

local notation "K" => FractionRing A
local notation "L" => FractionRing B

private theorem genericBasis_apply {ι : Type*} (b : Basis ι A B) (j : ι) :
    genericBasis A B b j = algebraMap B L (b j) := by
  letI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization_of_isSeparable A K L B
  unfold genericBasis
  exact b.localizationLocalization_apply K A⁰ L j

/-- Construct the integral tensor with product a. The diagonal identity is
proved by the transpose of the multiplication matrix on the same basis. -/
theorem exists_integral_trace_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι A B) (a : B) (ha : a ∈ differentIdeal A B) :
    ∃ C : B ⊗[A] B,
      TensorProduct.lmul' (S := B) A C = a ∧
      ∀ x : B, ((1 : B) ⊗ₜ[A] x - x ⊗ₜ[A] (1 : B)) * C = 0 := by
  obtain ⟨c, hc⟩ := exists_scaled_traceDual A B b a ha
  let bK := genericBasis A B b
  have hbK (j : ι) : bK j = algebraMap B L (b j) := genericBasis_apply b j
  have coefficient (x : B) (i : ι) :
      x * c i = ∑ j, (b.repr (x * b j) i) • c j := by
    have hre (j : ι) :
        bK.repr ((algebraMap B L x) * bK j) i = algebraMap A K (b.repr (x * b j) i) := by
      rw [hbK j, ← map_mul]
      exact repr_algebraMap A B b (x * b j) i
    have h_expand :
        (algebraMap B L x) * bK.traceDual i =
          ∑ j, bK.repr ((algebraMap B L x) * bK j) i • bK.traceDual j := by
      rw [← (bK.traceDual).sum_repr ((algebraMap B L x) * bK.traceDual i)]
      simp only [traceDual_repr_mul]
    apply IsFractionRing.injective B L
    simp only [map_mul, map_sum, Algebra.smul_def, hc, ← IsScalarTower.algebraMap_apply A B L]
    change algebraMap B L x * (algebraMap B L a * bK.traceDual i) =
      ∑ j, algebraMap A L (b.repr (x * b j) i) * (algebraMap B L a * bK.traceDual j)
    calc
      _ = algebraMap B L a * ((algebraMap B L x) * bK.traceDual i) := by ac_rfl
      _ = _ := by
        rw [h_expand, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [hre j, Algebra.smul_def, ← IsScalarTower.algebraMap_apply A K L]
        ac_rfl
  let C : B ⊗[A] B := ∑ i, b i ⊗ₜ[A] c i
  refine ⟨C, ?_, ?_⟩
  · simp only [C, map_sum, TensorProduct.lmul'_apply_tmul]
    apply IsFractionRing.injective B L
    simp only [map_sum, map_mul, hc, ← hbK]
    change (∑ i, bK i * (algebraMap B L a * bK.traceDual i)) = algebraMap B L a
    calc
      _ = algebraMap B L a * (∑ i, bK i * bK.traceDual i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
      _ = _ := by rw [sum_mul_traceDual, mul_one]
  · intro x
    have move : ((1 : B) ⊗ₜ[A] x) * C = (x ⊗ₜ[A] (1 : B)) * C := by
      calc
        _ = ∑ i, b i ⊗ₜ[A] (x * c i) := by
          simp only [C, Finset.mul_sum, TensorProduct.tmul_mul_tmul, one_mul]
        _ = ∑ i, ∑ j, ((b.repr (x * b j) i) • b i) ⊗ₜ[A] c j := by
          simp only [coefficient x, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul']
        _ = ∑ j, (x * b j) ⊗ₜ[A] c j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [← TensorProduct.sum_tmul, b.sum_repr]
        _ = _ := by
          simp only [C, Finset.mul_sum, TensorProduct.tmul_mul_tmul, one_mul]
    rw [sub_mul, move, sub_self]

/-- The CRT multiplier can now be consumed by any derivation over the same
structural j-line. No separate monogenic presentation is assumed. -/
theorem different_smul_derivation_eq_zero {ι T : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup T] [Module A T] [Module B T] [IsScalarTower A B T]
    (b : Basis ι A B) (a : B) (ha : a ∈ differentIdeal A B) (D : Derivation A B T) (x : B) :
    a • D x = 0 := by
  obtain ⟨C, hm, hd⟩ := exists_integral_trace_diagonal b a ha
  exact SelectedJTraceDiagonalDerivation318.smul_derivation_eq_zero D C a hm hd x

end SelectedJDifferentAnnihilates318

#print axioms SelectedJDifferentAnnihilates318.exists_integral_trace_diagonal
#print axioms SelectedJDifferentAnnihilates318.different_smul_derivation_eq_zero
