module
public import ActualInfinitySquareZero318
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section

namespace ActualNonSplitIdealChart318
open InfinityChart318 ActualInfinitySquareZero318
universe u

variable (R : Type u) {T : Type u} [CommRing R] [CommRing T] [Algebra R T]

abbrev Direction (I : Ideal T) := ↥((I : Submodule T T).restrictScalars R)

instance oppositeDirection (I : Ideal T) : Module Rᵐᵒᵖ (Direction R I) :=
  Module.compHom (Direction R I) (RingEquiv.toOpposite R).symm.toRingHom

instance centralDirection (I : Ideal T) : IsCentralScalar R (Direction R I) where
  op_smul_eq_smul _ _ := rfl

/-- Products of the two *actual* ideal directions vanish in T. -/
theorem mul_zero_of_mem (I : Ideal T) (hI : I ^ 2 = ⊥)
    {x y : T} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have h : x * y ∈ I * I := Ideal.mul_mem_mul hx hy
  rw [← pow_two, hI] at h
  exact Ideal.mem_bot.mp h

/-- Canonical map R⊕I→T. It only uses the given R-algebra and ideal
inclusion; the quotient T/I is not assumed to have a section. -/
@[expose] def specimen (I : Ideal T) (hI : I ^ 2 = ⊥) :
    TrivSqZeroExt R (Direction R I) →ₐ[R] T :=
  TrivSqZeroExt.liftEquivOfComm
    ⟨((I : Submodule T T).restrictScalars R).subtype,
      fun a b => mul_zero_of_mem I hI a.property b.property⟩

@[simp] theorem specimen_inr (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction R I) :
    specimen R I hI (TrivSqZeroExt.inr a) = (a : T) := by
  rw [specimen, TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inr] <;> rfl

/-- The actual first-order infinity point on T is the image of the
canonical split specimen, not a choice of lift from the quotient. -/
@[expose] def idealChart (A B : R) (I : Ideal T) (hI : I ^ 2 = ⊥)
    (a : Direction R I) : Ring A B →ₐ[R] T :=
  (specimen R I hI).comp (jet A B a)

@[simp] theorem idealChart_x (A B : R) (I : Ideal T) (hI : I ^ 2 = ⊥)
    (a : Direction R I) : idealChart R A B I hI a (x A B) = (a : T) := by
  simp only [idealChart, AlgHom.comp_apply, jet_x, specimen_inr]

@[simp] theorem idealChart_z (A B : R) (I : Ideal T) (hI : I ^ 2 = ⊥)
    (a : Direction R I) : idealChart R A B I hI a (z A B) = 0 := by
  simp only [idealChart, AlgHom.comp_apply, jet_z, map_zero]

theorem idealChart_mod (A B : R) (I : Ideal T) (hI : I ^ 2 = ⊥)
    (a : Direction R I) : (Ideal.Quotient.mkₐ R I).comp (idealChart R A B I hI a) =
      (Algebra.ofId R (T ⧸ I)).comp (origin A B) := by
  apply InfinityChart318.hom_ext
  · change Ideal.Quotient.mk I (idealChart R A B I hI a (x A B)) =
      algebraMap R (T ⧸ I) (origin A B (x A B))
    rw [idealChart_x, origin_x, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property
  · simp only [AlgHom.comp_apply, idealChart_z, origin_z, map_zero]

theorem idealChart_injective (A B : R) (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Injective (idealChart R A B I hI) := by
  intro a b hab
  apply Subtype.ext
  simpa only [idealChart_x] using congrArg (fun f : Ring A B →ₐ[R] T => f (x A B)) hab

/-- Every actual chart point reducing to the identity is of this form,
also for a non-split coefficient quotient. -/
theorem exists_idealChart (A B : R) (I : Ideal T) (hI : I ^ 2 = ⊥)
    (f : Ring A B →ₐ[R] T)
    (hf : (Ideal.Quotient.mkₐ R I).comp f =
      (Algebra.ofId R (T ⧸ I)).comp (origin A B)) :
    ∃ a : Direction R I, f = idealChart R A B I hI a := by
  have hmem (q : Ring A B) (hq : origin A B q = 0) : f q ∈ I := by
    have he := congrArg (fun g : Ring A B →ₐ[R] (T ⧸ I) => g q) hf
    change Ideal.Quotient.mk I (f q) = algebraMap R (T ⧸ I) (origin A B q) at he
    rw [hq, map_zero] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  have hx := hmem (x A B) (origin_x A B)
  have hz := hmem (z A B) (origin_z A B)
  have x₂ : (f (x A B)) ^ 2 = 0 := by
    rw [pow_two]
    exact mul_zero_of_mem I hI hx hx
  have z₂ : (f (z A B)) ^ 2 = 0 := by
    rw [pow_two]
    exact mul_zero_of_mem I hI hz hz
  have x₃ : (f (x A B)) ^ 3 = 0 := by rw [pow_succ, x₂, zero_mul]
  have z₃ : (f (z A B)) ^ 3 = 0 := by rw [pow_succ, z₂, zero_mul]
  have hrel := congrArg f (relation A B)
  have hfz : f (z A B) = 0 := by
    simpa only [map_sub, map_mul, map_pow, map_zero, x₃, z₂, z₃, mul_zero, sub_zero] using hrel
  refine ⟨⟨f (x A B), hx⟩, InfinityChart318.hom_ext A B ?_ ?_⟩
  · rw [idealChart_x] <;> rfl
  · rw [idealChart_z]
    exact hfz

end ActualNonSplitIdealChart318
