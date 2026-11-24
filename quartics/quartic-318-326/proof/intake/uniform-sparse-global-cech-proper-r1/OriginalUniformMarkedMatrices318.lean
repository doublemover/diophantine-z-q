module
public import OriginalUniformMarkedQMSurface318
public import Mathlib.LinearAlgebra.Matrix.Notation
public section
namespace OriginalUniformMarkedMatrices318
open Matrix OriginalUniformMarkedQMSurface318 OriginalUniformSparseJet318
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]
abbrev M2 (K : Type*) := Matrix (Fin 2) (Fin 2) K
@[expose] def jMat (v : K) : M2 K := !![v,0;0,-v]
@[expose] def gMat (u : K) : M2 K := !![0,u;42/u,0]
@[expose] def diagForm (L M : K) : M2 K := !![L,0;0,M]
@[expose] def splitRow (v u a b c d : K) : M2 K := !![a+b*v,(c+d*v)*u;(c-d*v)*(42/u),a-b*v]
structure Action (v u L M : K) : Prop where
  j_square : jMat v*jMat v=(5:K) • (1:M2 K)
  g_square : gMat u*gMat u=(42:K) • (1:M2 K)
  anticommute : jMat v*gMat u= -(gMat u*jMat v)
  sym_j : (jMat v).transpose*diagForm L M=diagForm L M*jMat v
  sym_g : (gMat u).transpose*diagForm L M=diagForm L M*gMat u
  spanning : ∀ Z : M2 K,∃ a b c d : K,splitRow v u a b c d=Z
  determinant : ∀ a b c d : K,(splitRow v u a b c d).det=a^2-5*b^2-42*c^2+210*d^2
theorem split_action [CharZero K] (v u L M : K) (hv : v^2=5) (hu : u≠0) (hs : u^2*L=42*M) :
    Action v u L M := by
  have hvn : v≠0 := fun hh => by rw [hh] at hv; norm_num at hv
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [jMat,Matrix.smul_apply,Matrix.one_apply,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals linear_combination hv
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [gMat,Matrix.smul_apply,Matrix.one_apply,Matrix.mul_apply,Fin.sum_univ_two,hu]
    all_goals field_simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp [jMat,gMat,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [jMat,diagForm,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [gMat,diagForm,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals field_simp
    all_goals first | linear_combination hs | linear_combination -hs
  · intro Z
    refine ⟨(Z 0 0+Z 1 1)/2,(Z 0 0-Z 1 1)/(2*v),(Z 0 1/u+Z 1 0*u/42)/2,(Z 0 1/u-Z 1 0*u/42)/(2*v),?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [splitRow] <;> field_simp <;> ring
  · intro a b c d
    simp [splitRow,Matrix.det_fin_two]
    field_simp
    linear_combination (-b^2+42*d^2)*hv
theorem on_sheet [CharZero K] (d : Row K) (R u v : K) (hv : v^2=5) (h : Sheet d R u) :
    Action v u (V0 d.m d.p d.q R) (V2 d.m d.p d.q R) := split_action v u _ _ hv h.u_ne h.self_adjoint
end OriginalUniformMarkedMatrices318
#print axioms OriginalUniformMarkedMatrices318.on_sheet
