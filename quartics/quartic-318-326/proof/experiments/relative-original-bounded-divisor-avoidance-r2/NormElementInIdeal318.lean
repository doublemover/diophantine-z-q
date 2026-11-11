module
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public section
noncomputable section
open scoped Matrix
namespace NormElementInIdeal318
universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Free R S]

/-- The actual determinant norm of an element of an ideal stays in that
ideal after its original scalar map. The adjugate constructs the multiplier,
so no radical or norm-of-ideal surrogate is involved. -/
lemma norm_mem (I : Ideal S) (a : S) (ha : a∈I) :
    algebraMap R S (Algebra.norm R a) ∈ I := by
  classical
  let b := Module.Free.chooseBasis R S
  let e := b.equivFun
  let M := Algebra.leftMulMatrix b a
  let y := e.symm (M.adjugate *ᵥ e 1)
  have hm : a*y=algebraMap R S (Algebra.norm R a) := by
    apply e.injective
    have hv : M *ᵥ e y=e (a*y) := Algebra.leftMulMatrix_mulVec_repr b a y
    rw [← hv]
    simp only [y,LinearEquiv.apply_symm_apply,Matrix.mulVec_mulVec,
      Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]
    rw [show algebraMap R S (Algebra.norm R a)=(Algebra.norm R a) • (1:S) by
      simp only [Algebra.smul_def,mul_one],map_smul,
      Algebra.norm_eq_matrix_det b]
  rw [← hm]
  exact I.mul_mem_right y ha

/-- A nonzero element of an actual ideal in a finite free domain algebra
therefore supplies a NONZERO original scalar in that same ideal. -/
lemma nonzero_scalar [IsDomain R] [IsDomain S] (I : Ideal S)
    (a : S) (ha : a∈I) (hne : a≠0) :
    ∃ r : R, r≠0 ∧ algebraMap R S r∈I :=
  ⟨Algebra.norm R a,Algebra.norm_ne_zero_iff.mpr hne,norm_mem R S I a ha⟩
end NormElementInIdeal318
