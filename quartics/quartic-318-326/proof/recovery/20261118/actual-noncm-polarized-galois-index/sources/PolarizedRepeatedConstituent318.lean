module
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic
public section
namespace PolarizedRepeatedConstituent318
open Matrix
variable {k : Type*} [Field k]
abbrev M₂ (k : Type*) := Matrix (Fin 2) (Fin 2) k

/-- All alternating pairings on a two-dimensional space in a basis,
including a zero restriction on an isotropic summand. -/
def alt (a : k) : M₂ k := !![0,a;-a,0]

private theorem det_alt (a:k) : (alt a).det=a^2 := by
  rw [Matrix.det_fin_two]
  simp [alt] <;> ring

private theorem block_square (R U : M₂ k) (v : k) (hU : U.det≠0)
    (hs : R.transpose*U*R=v • U) : R.det^2=v^2 := by
  have h := congrArg Matrix.det hs
  simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_smul,Fintype.card_fin] at h
  apply mul_right_cancel₀ hU
  linear_combination h

/-- In a basis adapted to the two identical constituents, preservation of the
nondegenerate alternating pairing up to multiplier proves det(r)^2=χ^2,
including when both summands are totally isotropic. This avoids the
extraneous fourth-root ambiguity left by taking the ambient determinant. -/
theorem square (R X Y : M₂ k) (a b v : k)
    (hne : (Matrix.fromBlocks (alt a) X Y (alt b)).det≠0)
    (hs : (Matrix.fromBlocks R 0 0 R).transpose *
      (Matrix.fromBlocks (alt a) X Y (alt b)) * (Matrix.fromBlocks R 0 0 R) =
      v • Matrix.fromBlocks (alt a) X Y (alt b)) : R.det^2=v^2 := by
  classical
  simp only [Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.fromBlocks_multiply,
    mul_zero,zero_mul,add_zero,zero_add,Matrix.fromBlocks_smul,Matrix.fromBlocks_inj] at hs
  by_cases ha : a=0
  · by_cases hb : b=0
    · subst a; subst b
      have ha0 : alt (0:k)=0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [alt]
      rw [ha0] at hne
      let S := Matrix.fromBlocks (0:M₂ k) 1 1 (0:M₂ k)
      have hS : S*S=1 := by simp [S,Matrix.fromBlocks_multiply,Matrix.fromBlocks_one]
      have hS' : S.det≠0 := by
        intro h
        have hd := congrArg Matrix.det hS
        simp [Matrix.det_mul,h] at hd
      have hprod : ((Matrix.fromBlocks (0:M₂ k) X Y (0:M₂ k))*S).det≠0 := by
        rw [Matrix.det_mul];exact mul_ne_zero hne hS'
      have hXY : X.det*Y.det≠0 := by
        simpa [S,Matrix.fromBlocks_multiply,Matrix.det_fromBlocks_zero₂₁] using hprod
      exact block_square R X v (left_ne_zero_of_mul hXY) hs.2.1
    · exact block_square R (alt b) v (by rw [det_alt];exact pow_ne_zero _ hb) hs.2.2.2
  · exact block_square R (alt a) v (by rw [det_alt];exact pow_ne_zero _ ha) hs.1
end PolarizedRepeatedConstituent318
