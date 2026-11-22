module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# Flat coefficients of the actual dual-number affine charts

This is the ring/module producer for a smooth chart of the pulled family over the dual numbers.
Its flatness is over that dual-number base, not over the later ramified arithmetic trait.
-/

public section

open TensorProduct MulOpposite
open scoped TensorProduct

namespace SelectedSameADualNumberFlatCoefficient318

variable (k : Type*) [CommRing k]

/-- The actual generator of the nilpotent direction of the dual-number base. -/
def epsilon : TrivSqZeroExt k k := TrivSqZeroExt.inr 1

theorem epsilon_square : epsilon k * epsilon k = 0 := by
  unfold epsilon
  exact TrivSqZeroExt.inr_mul_inr k 1 1

private theorem epsilon_mul (x : TrivSqZeroExt k k) :
    epsilon k * x = TrivSqZeroExt.inr x.fst := by
  apply TrivSqZeroExt.ext
  · simp [epsilon]
  · simp [epsilon, op_smul_eq_smul]

private def epsMul : TrivSqZeroExt k k →ₗ[TrivSqZeroExt k k] TrivSqZeroExt k k where
  toFun x := epsilon k * x
  map_add' x y := mul_add _ _ _
  map_smul' r x := by
    change epsilon k * (r * x) = r * (epsilon k * x)
    rw [← mul_assoc, mul_comm (epsilon k) r, mul_assoc]

private theorem epsMul_apply (x : TrivSqZeroExt k k) :
    epsMul k x = epsilon k * x := rfl

private theorem base_exact : Function.Exact (epsMul k) (epsMul k) := by
  intro x
  change epsilon k * x = 0 ↔ ∃ y, epsilon k * y = x
  constructor
  · intro hx
    have hfst : x.fst = 0 := by
      have h := congrArg (TrivSqZeroExt.snd : TrivSqZeroExt k k → k)
        ((epsilon_mul k x).symm.trans hx)
      simpa using h
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [epsilon_mul, TrivSqZeroExt.fst_inl]
    apply TrivSqZeroExt.ext
    · simpa using hfst.symm
    · simp
  · rintro ⟨y, rfl⟩
    rw [← mul_assoc, epsilon_square, zero_mul]

variable (M : Type*) [AddCommGroup M] [Module (TrivSqZeroExt k k) M]

private theorem rid_tensor_eps
    (x : M ⊗[TrivSqZeroExt k k] TrivSqZeroExt k k) :
    TensorProduct.rid (TrivSqZeroExt k k) M ((epsMul k).lTensor M x) =
      epsilon k • TensorProduct.rid (TrivSqZeroExt k k) M x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m a =>
    rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, TensorProduct.rid_tmul,
      epsMul_apply, mul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]

/-- Exactness of multiplication by the dual-number generator on a genuinely flat module. -/
theorem epsilon_smul_eq_zero_iff [Module.Flat (TrivSqZeroExt k k) M] (m : M) :
    epsilon k • m = 0 ↔ ∃ n : M, epsilon k • n = m := by
  constructor
  · intro hm
    let e := TensorProduct.rid (TrivSqZeroExt k k) M
    let t := e.symm m
    have her : e t = m := e.apply_symm_apply m
    have ht : (epsMul k).lTensor M t = 0 := by
      apply e.injective
      change TensorProduct.rid (TrivSqZeroExt k k) M ((epsMul k).lTensor M t) =
        TensorProduct.rid (TrivSqZeroExt k k) M 0
      rw [rid_tensor_eps, map_zero]
      change epsilon k • e t = 0
      rw [her, hm]
    have he := Module.Flat.lTensor_exact M (base_exact k)
    obtain ⟨y, hy⟩ := (he t).mp ht
    refine ⟨e y, ?_⟩
    calc
      epsilon k • e y = e ((epsMul k).lTensor M y) := (rid_tensor_eps k M y).symm
      _ = e t := congrArg e hy
      _ = m := her
  · rintro ⟨n, rfl⟩
    rw [← mul_smul, epsilon_square]
    exact zero_smul (TrivSqZeroExt k k) n

variable (C : Type*) [CommRing C] [Algebra (TrivSqZeroExt k k) C]

/-- The same square-zero generator in the affine chart ring. -/
def epsilonIn : C := algebraMap (TrivSqZeroExt k k) C (epsilon k)

theorem epsilonIn_square : epsilonIn k C * epsilonIn k C = 0 := by
  unfold epsilonIn
  rw [← map_mul, epsilon_square, map_zero]

/-- Given the genuine principal reduction of the affine and a section of that reduction,
the nilpotent coefficient exists and is unique. We do not assume an affine trivialization. -/
theorem existsUnique_coefficient [Module.Flat (TrivSqZeroExt k k) C]
    {B : Type*} [CommRing B] (ρ : C →+* B) (s : B →+* C) (hs : ∀ b, ρ (s b) = b)
    (hker : RingHom.ker ρ = Ideal.span ({epsilonIn k C} : Set C))
    (z : C) (hz : ρ z = 0) :
    ∃! b : B, epsilonIn k C * s b = z := by
  let e := epsilonIn k C
  have he : e * e = 0 := epsilonIn_square k C
  have hz' : z ∈ Ideal.span ({e} : Set C) := by
    change z ∈ Ideal.span ({epsilonIn k C} : Set C)
    rw [← hker]
    exact RingHom.mem_ker.mpr hz
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz'
  have hd : w - s (ρ w) ∈ RingHom.ker ρ := RingHom.mem_ker.mpr (by rw [map_sub, hs, sub_self])
  rw [hker] at hd
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hd
  have h0 : e * (w - s (ρ w)) = 0 := by
    rw [hv, ← mul_assoc, he, zero_mul]
  have heq : e * s (ρ w) = z := by
    rw [hw]
    exact (sub_eq_zero.mp (by simpa only [mul_sub] using h0)).symm
  refine ⟨ρ w, heq, ?_⟩
  intro b hb
  have h0b : e * (s b - s (ρ w)) = 0 := by rw [mul_sub, hb, heq, sub_self]
  have hact : epsilon k • (s b - s (ρ w)) = 0 := by
    simpa only [Algebra.smul_def, epsilonIn, e] using h0b
  obtain ⟨u, hu⟩ := (epsilon_smul_eq_zero_iff k C _).mp hact
  have hmem : s b - s (ρ w) ∈ Ideal.span ({epsilonIn k C} : Set C) := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨u, ?_⟩
    simpa only [Algebra.smul_def, epsilonIn] using hu.symm
  rw [← hker] at hmem
  have hb' := RingHom.mem_ker.mp hmem
  simpa only [map_sub, hs, sub_eq_zero] using hb'

end SelectedSameADualNumberFlatCoefficient318
