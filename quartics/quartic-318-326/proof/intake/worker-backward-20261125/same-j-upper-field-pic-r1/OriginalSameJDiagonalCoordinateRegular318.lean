module
public import OriginalSameJDiagonalEquationFibre318
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section
noncomputable section

namespace OriginalSameJDiagonalCoordinateRegular318

open Algebra Polynomial
open OriginalSameJDiagonalEquationFibre318 (coordinateDifference χ)
open scoped TensorProduct nonZeroDivisors
universe u

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [Algebra k[X] A] [IsScalarTower k k[X] A]

abbrev D := k[X]
abbrev B := D (k:=k) ⊗[k] A

def before : B (k:=k) (A:=A) :=
  (X:k[X])⊗ₜ[k](1:A) - (1:k[X])⊗ₜ[k]χ (k:=k) (A:=A)

abbrev polynomialRead : B (k:=k) (A:=A) ≃ₐ[k] A[X] :=
  (Algebra.TensorProduct.comm k k[X] A).trans (polyEquivTensor k A).symm

theorem literally_monic :
    polynomialRead (k:=k) (A:=A) (before (k:=k) (A:=A)) =
      (X:A[X]) - C (χ (k:=k) (A:=A)) := by
  have l : polynomialRead (k:=k) (A:=A) ((X:k[X])⊗ₜ[k](1:A)) = X := by
    change (polyEquivTensor k A).symm ((1:A)⊗ₜ[k](X:k[X])) = X
    simp only [polyEquivTensor_symm_apply_tmul_eq_smul,Polynomial.map_X,one_smul]
  have r : polynomialRead (k:=k) (A:=A) ((1:k[X])⊗ₜ[k]χ (k:=k) (A:=A)) =
      C (χ (k:=k) (A:=A)) := by
    change (polyEquivTensor k A).symm (χ (k:=k) (A:=A)⊗ₜ[k](1:k[X])) = _
    rw [polyEquivTensor_symm_apply_tmul_eq_smul,Polynomial.map_one]
    change C (χ (k:=k) (A:=A)) * 1 = C (χ (k:=k) (A:=A))
    exact mul_one _
  rw [before,map_sub,l,r]

private theorem before_regular (b : B (k:=k) (A:=A))
    (h : b * before (k:=k) (A:=A) = 0) : b=0 := by
  let p := polynomialRead (k:=k) (A:=A)
  apply p.injective
  have ht : p b * ((X:A[X]) - C (χ (k:=k) (A:=A))) = 0 := by
    rw [← literally_monic,← map_mul,h,map_zero]
  have hmem := (Polynomial.monic_X_sub_C (χ (k:=k) (A:=A))).mem_nonZeroDivisors
  exact ((mem_nonZeroDivisors_iff_right.mp hmem) _ ht).trans (map_zero p).symm

abbrev twoBase : A ⊗[k[X]] B (k:=k) (A:=A) ≃ₐ[k[X]] A⊗[k]A :=
  Algebra.TensorProduct.cancelBaseChange k k[X] k[X] A A

theorem twoBase_equation :
    twoBase (k:=k) (A:=A) ((1:A)⊗ₜ[k[X]]before (k:=k) (A:=A)) =
      coordinateDifference (k:=k) (A:=A) := by
  rw [before,TensorProduct.tmul_sub,map_sub,Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  simp only [Algebra.smul_def,mul_one,map_one,coordinateDifference,χ]

/-- The two-coordinate difference of the very same étale χ chart is
regular by base change of multiplication by the monic X-C(χ). No
geometric integrality, rational support point or reduced test enters. -/
theorem regular [Module.Flat k[X] A] (z : A⊗[k]A)
    (hz : z*coordinateDifference (k:=k) (A:=A) = 0) : z=0 := by
  let m := LinearMap.mulRight k[X] (before (k:=k) (A:=A))
  have hm : Function.Injective m := by
    intro a b h
    apply sub_eq_zero.mp
    apply before_regular
    rw [sub_mul,sub_eq_zero]
    exact h
  have hT : Function.Injective (m.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap m hm
  let e := twoBase (k:=k) (A:=A)
  let y := (1:A)⊗ₜ[k[X]]before (k:=k) (A:=A)
  have reads (v : A ⊗[k[X]] B (k:=k) (A:=A)) : m.lTensor A v = v*y := by
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero,zero_mul]
    | tmul a b =>
      simp only [y,LinearMap.lTensor_tmul,m,LinearMap.mulRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul,mul_one]
    | add a b ha hb => rw [map_add,add_mul,ha,hb]
  have h' : (m.lTensor A) (e.symm z) = (m.lTensor A) 0 := by
    apply e.injective
    rw [reads,map_zero,map_zero,map_mul,AlgEquiv.apply_symm_apply]
    change z * (twoBase (k:=k) (A:=A) ((1:A)⊗ₜ[k[X]]before (k:=k) (A:=A))) = 0
    rw [twoBase_equation]
    exact hz
  calc
    z = e (e.symm z) := (e.apply_symm_apply z).symm
    _ = e 0 := congrArg e (hT h')
    _ = 0 := map_zero e

end OriginalSameJDiagonalCoordinateRegular318

#print axioms OriginalSameJDiagonalCoordinateRegular318.literally_monic
#print axioms OriginalSameJDiagonalCoordinateRegular318.twoBase_equation
#print axioms OriginalSameJDiagonalCoordinateRegular318.regular
