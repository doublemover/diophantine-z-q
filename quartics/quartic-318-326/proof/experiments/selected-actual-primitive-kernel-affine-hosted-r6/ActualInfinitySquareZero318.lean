module
public import InfinityChart318
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Prod
public section
noncomputable section

namespace ActualInfinitySquareZero318
open InfinityChart318

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
  [IsCentralScalar R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M'] [Module Rᵐᵒᵖ M']
  [IsCentralScalar R M']

abbrev S (R : Type u) (M : Type v) := TrivSqZeroExt R M

/-- A genuine first-order lift of the infinity section has x in the
square-zero ideal and z equal to zero. Use the original Y=1 equation. -/
@[expose] def jet (A B : R) (a : M) : Ring A B →ₐ[R] S R M :=
  lift A B (TrivSqZeroExt.inr a) 0 (by
    have h₂ : (TrivSqZeroExt.inr a : S R M) ^ 2 = 0 := by
      rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    have h₃ : (TrivSqZeroExt.inr a : S R M) ^ 3 = 0 := by
      rw [pow_succ, h₂, zero_mul]
    simp [h₃])

@[simp] theorem jet_x (A B : R) (a : M) :
    jet A B a (x A B) = TrivSqZeroExt.inr a := lift_x ..

@[simp] theorem jet_z (A B : R) (a : M) :
    jet A B a (z A B) = 0 := lift_z ..

@[simp] theorem augmentation_jet (A B : R) (a : M) :
    (TrivSqZeroExt.fstHom R R M).comp (jet A B a) = origin A B := by
  apply InfinityChart318.hom_ext
  · change (jet A B a (x A B)).fst = origin A B (x A B)
    rw [jet_x, TrivSqZeroExt.fst_inr, origin_x]
  · change (jet A B a (z A B)).fst = origin A B (z A B)
    rw [jet_z, TrivSqZeroExt.fst_zero, origin_z]

theorem jet_zero (A B : R) :
    jet A B (0 : M) = (Algebra.ofId R (S R M)).comp (origin A B) := by
  apply InfinityChart318.hom_ext <;> simp

/-- Classify every lifted infinity point, not just the constructed ones. -/
theorem eq_jet_of_augmentation (A B : R) (f : Ring A B →ₐ[R] S R M)
    (hf : (TrivSqZeroExt.fstHom R R M).comp f = origin A B) :
    f = jet A B (f (x A B)).snd := by
  have hs (c : Ring A B) : (f c).fst = origin A B c :=
    congrArg (fun g : Ring A B →ₐ[R] R => g c) hf
  have hx : f (x A B) = TrivSqZeroExt.inr (f (x A B)).snd :=
    TrivSqZeroExt.ext ((hs _).trans (origin_x A B)) rfl
  have hz : f (z A B) = TrivSqZeroExt.inr (f (z A B)).snd :=
    TrivSqZeroExt.ext ((hs _).trans (origin_z A B)) rfl
  have x₂ : (f (x A B)) ^ 2 = 0 := by rw [hx, pow_two, TrivSqZeroExt.inr_mul_inr]
  have z₂ : (f (z A B)) ^ 2 = 0 := by rw [hz, pow_two, TrivSqZeroExt.inr_mul_inr]
  have x₃ : (f (x A B)) ^ 3 = 0 := by rw [pow_succ, x₂, zero_mul]
  have z₃ : (f (z A B)) ^ 3 = 0 := by rw [pow_succ, z₂, zero_mul]
  have hrel := congrArg f (relation A B)
  have hfz : f (z A B) = 0 := by
    simpa only [map_sub, map_mul, map_pow, map_zero, x₃, z₂, z₃, mul_zero, sub_zero] using hrel
  apply InfinityChart318.hom_ext
  · simpa only [jet_x] using hx
  · simpa only [jet_z] using hfz

theorem jet_injective (A B : R) : Function.Injective (jet A B : M → Ring A B →ₐ[R] S R M) := by
  intro a b h
  simpa only [jet_x, TrivSqZeroExt.snd_inr] using
    congrArg (fun f : Ring A B →ₐ[R] S R M => (f (x A B)).snd) h

/-- The same chart jet changes only by the specified module map. -/
theorem map_jet (A B : R) (l : M →ₗ[R] M') (a : M) :
    (TrivSqZeroExt.map l).comp (jet A B a) = jet A B (l a) := by
  apply InfinityChart318.hom_ext <;>
    simp only [AlgHom.comp_apply, jet_x, jet_z, TrivSqZeroExt.map_inr, map_zero]

end ActualInfinitySquareZero318
