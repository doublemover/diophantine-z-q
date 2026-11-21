module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

noncomputable section

namespace SelectedActualAbelFiberCharacterSpectrum318

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- A nonunit in the literal finite complex fibre supplies a complex
character of this same algebra. The argument works with nilpotents:
take a maximal ideal, then lift the finite residue field into ℂ. -/
theorem exists_character_of_nonunit_sub [Module.Finite ℂ B]
    (b : B) (u : ℂ) (h : ¬ IsUnit (algebraMap ℂ B u - b)) :
    ∃ f : B →ₐ[ℂ] ℂ, f b = u := by
  let z : B := algebraMap ℂ B u - b
  let I : Ideal B := Ideal.span ({z} : Set B)
  have hI : I ≠ ⊤ :=
    fun e => h ((Ideal.span_singleton_eq_top (x := z)).1 e)
  obtain ⟨m,hm,hle⟩ := Ideal.exists_le_maximal I hI
  letI : m.IsMaximal := hm
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let q : B →ₐ[ℂ] (B ⧸ m) := Ideal.Quotient.mkₐ ℂ m
  letI : Module.Finite ℂ (B ⧸ m) :=
    Module.Finite.of_surjective q.toLinearMap (Ideal.Quotient.mkₐ_surjective ℂ m)
  let i : (B ⧸ m) →ₐ[ℂ] ℂ := IsAlgClosed.lift
  let f := i.comp q
  have hz : z ∈ I := Ideal.subset_span (Set.mem_singleton z)
  have he : q z = 0 := by
    change Ideal.Quotient.mk m z = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle hz)
  have hf : f z = 0 := (congrArg i he).trans (map_zero i)
  have hu : u - f b = 0 := by
    simpa only [z, map_sub, f.commutes, Algebra.algebraMap_self_apply] using hf
  exact ⟨f, (sub_eq_zero.mp hu).symm⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (basis : Module.Basis ι ℂ B)

private theorem left_mul_scalar_sub (b : B) (u : ℂ) :
    Algebra.leftMulMatrix basis (algebraMap ℂ B u - b) =
      Matrix.scalar ι u - Algebra.leftMulMatrix basis b := by
  simp only [map_sub, (Algebra.leftMulMatrix basis).commutes,
    Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, Algebra.algebraMap_self_apply,
    Matrix.scalar_apply]

private theorem left_mul_isUnit_iff (b : B) :
    IsUnit (Algebra.leftMulMatrix basis b) ↔ IsUnit b := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.isUnit_toMatrix_iff]
  exact Algebra.lmul_isUnit_iff

/-- The roots of the characteristic polynomial of actual multiplication
are the values at actual complex characters of the same finite fibre.
This is a set-of-values statement, allowing repeated roots and a
nonreduced fibre. -/
theorem determinant_zero_iff_character (b : B) (u : ℂ) :
    (Matrix.scalar ι u - Algebra.leftMulMatrix basis b).det = 0 ↔
      ∃ f : B →ₐ[ℂ] ℂ, f b = u := by
  let z : B := algebraMap ℂ B u - b
  have he : Algebra.leftMulMatrix basis z =
      Matrix.scalar ι u - Algebra.leftMulMatrix basis b := left_mul_scalar_sub basis b u
  rw [← he]
  constructor
  · intro h
    letI : Module.Finite ℂ B := basis.finiteDimensional_of_finite
    apply exists_character_of_nonunit_sub b u
    intro hu
    have hU : IsUnit (Algebra.leftMulMatrix basis z) := (left_mul_isUnit_iff basis z).2 hu
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero h
  · rintro ⟨f,h⟩
    by_contra hdet
    have hCol : IsUnit (Algebra.leftMulMatrix basis z) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hdet)
    have hU : IsUnit z := (left_mul_isUnit_iff basis z).1 hCol
    have hzero : f z = 0 := by
      simp only [z, map_sub, f.commutes, Algebra.algebraMap_self_apply, h, sub_self]
    exact (hU.map f.toRingHom).ne_zero hzero

end SelectedActualAbelFiberCharacterSpectrum318

#print axioms SelectedActualAbelFiberCharacterSpectrum318.exists_character_of_nonunit_sub
#print axioms SelectedActualAbelFiberCharacterSpectrum318.determinant_zero_iff_character
