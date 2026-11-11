module
public import Mathlib.Algebra.Quaternion
public import Mathlib.Tactic
public section
noncomputable section
namespace PELQuaternionAlgebra318
open QuaternionAlgebra
set_option maxHeartbeats 800000

/-- An explicit rational quaternion candidate with μ²=−210 and j²=5.
The reduced-discriminant/maximal-order identification is a separate theorem,
not encoded by the name or inferred from the dimension. -/
abbrev B := QuaternionAlgebra ℚ (-210) 0 5
@[expose] def mu : B := ⟨0,1,0,0⟩
@[expose] def j : B := ⟨0,0,1,0⟩
@[expose] def k : B := ⟨0,0,0,1⟩
@[expose] def muInverse : B := ⟨0,-1/210,0,0⟩

theorem mu_square : mu*mu=algebraMap ℚ B (-210) := by
  ext <;> norm_num [mu,QuaternionAlgebra.algebraMap_eq]
theorem j_square : j*j=algebraMap ℚ B 5 := by
  ext <;> norm_num [j,QuaternionAlgebra.algebraMap_eq]
theorem mu_j : mu*j=k := by ext <;> norm_num [mu,j,k]
theorem j_mu : j*mu= -k := by ext <;> norm_num [mu,j,k]
theorem mu_inverse_left : muInverse*mu=1 := by ext <;> norm_num [muInverse,mu]
theorem mu_inverse_right : mu*muInverse=1 := by ext <;> norm_num [muInverse,mu]

theorem dimension : Module.finrank ℚ B=4 := QuaternionAlgebra.finrank_eq_four _ _ _

/-- The positive-involution candidate has exactly the source convention
μ⁻¹·bar(x)·μ. It is not the standard quaternion conjugation. -/
@[expose] def rosati (x : B) : B := muInverse*star x*mu

theorem rosati_coordinates (x : B) : rosati x=⟨x.re,-x.imI,x.imJ,x.imK⟩ := by
  ext <;> simp [rosati,muInverse,mu] <;> ring

theorem rosati_involutive (x : B) : rosati (rosati x)=x := by
  rw [rosati_coordinates,rosati_coordinates]
  ext <;> simp

theorem rosati_add (x y : B) : rosati (x+y)=rosati x+rosati y := by
  simp only [rosati,star_add,mul_add,add_mul]

theorem rosati_mul (x y : B) : rosati (x*y)=rosati y*rosati x := by
  simp only [rosati_coordinates]
  ext <;> simp <;> ring

theorem rosati_scalar (q : ℚ) : rosati (algebraMap ℚ B q)=algebraMap ℚ B q := by
  rw [rosati_coordinates]
  ext <;> simp [QuaternionAlgebra.algebraMap_eq]

@[expose] def reducedTrace (x : B) : ℚ := 2*x.re
@[expose] def reducedNorm (x : B) : ℚ := x.re^2+210*x.imI^2-5*x.imJ^2-1050*x.imK^2

theorem norm_identity (x : B) : x*star x=algebraMap ℚ B (reducedNorm x) := by
  ext <;> simp [reducedNorm,QuaternionAlgebra.algebraMap_eq] <;> ring

theorem positive_trace_formula (x : B) :
    reducedTrace (x*rosati x)=2*(x.re^2+210*x.imI^2+5*x.imJ^2+1050*x.imK^2) := by
  rw [rosati_coordinates]
  simp [reducedTrace]
  ring

/-- Positivity is proved on the exact rational algebra and the exact source
involution, not postulated from an unrelated elliptic polarization. -/
theorem positive_trace (x : B) (hx : x≠0) : 0<reducedTrace (x*rosati x) := by
  rw [positive_trace_formula]
  have h0 := sq_nonneg x.re
  have h1 := sq_nonneg x.imI
  have h2 := sq_nonneg x.imJ
  have h3 := sq_nonneg x.imK
  by_contra h
  have hr : x.re=0 := by nlinarith
  have hi : x.imI=0 := by nlinarith
  have hj : x.imJ=0 := by nlinarith
  have hk : x.imK=0 := by nlinarith
  apply hx
  ext <;> assumption
end PELQuaternionAlgebra318
