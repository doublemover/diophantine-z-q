module
public import LiteralSecondSievePolynomial318
public section
noncomputable section
namespace LiteralPolynomialBasisEquiv318
open MvPolynomial LiteralSievePolynomial318
set_option maxHeartbeats 2000000

@[expose] def forwardVariables (q r A D : ℚ) (i : Fin 3) : Poly :=
  if i=0 then C r*X 0 else if i=1 then C (A*r)*X 0+C q*X 1
  else C (D*r)*X 0+C (q*r)*X 2
@[expose] def inverseVariables (q r A D : ℚ) (i : Fin 3) : Poly :=
  if i=0 then C r⁻¹*X 0 else if i=1 then C q⁻¹*(X 1-C A*X 0)
  else C (q*r)⁻¹*(X 2-C D*X 0)
@[expose] def forward (q r A D : ℚ) : Poly →ₐ[ℚ] Poly := aeval (forwardVariables q r A D)
@[expose] def backward (q r A D : ℚ) : Poly →ₐ[ℚ] Poly := aeval (inverseVariables q r A D)

lemma inverse_coefficient (q : ℚ) (hq : q≠0) : (C q⁻¹:Poly)*C q=1 := by
  rw [←map_mul,inv_mul_cancel₀ hq,map_one]

/-- Exact inverse composition on the polynomial generators. -/
theorem forward_backward (q r A D : ℚ) (hq : q≠0) (hr : r≠0) :
    (forward q r A D).comp (backward q r A D)=AlgHom.id ℚ Poly := by
  have hq' := inverse_coefficient q hq
  have hr' := inverse_coefficient r hr
  have hqr' := inverse_coefficient (q*r) (mul_ne_zero hq hr)
  simp only [map_mul] at hqr'
  ext i
  fin_cases i
  · simp [forward,backward,forwardVariables,inverseVariables,algebraMap_eq,map_mul]
    <;> linear_combination (X 0:Poly)*hr'
  · simp [forward,backward,forwardVariables,inverseVariables,algebraMap_eq,map_mul]
    <;> linear_combination (X 1:Poly)*hq'
  · simp [forward,backward,forwardVariables,inverseVariables,algebraMap_eq,map_mul]
    <;> linear_combination (X 2:Poly)*hqr'

/-- The opposite composition is also checked, with no determinant oracle. -/
theorem backward_forward (q r A D : ℚ) (hq : q≠0) (hr : r≠0) :
    (backward q r A D).comp (forward q r A D)=AlgHom.id ℚ Poly := by
  have hq' := inverse_coefficient q hq
  have hr' := inverse_coefficient r hr
  have hqr' := inverse_coefficient (q*r) (mul_ne_zero hq hr)
  simp only [map_mul] at hqr'
  ext i
  fin_cases i
  · simp [forward,backward,forwardVariables,inverseVariables,algebraMap_eq,map_mul]
    <;> linear_combination (X 0:Poly)*hr'
  · simp [forward,backward,forwardVariables,inverseVariables,algebraMap_eq,map_mul]
    <;> linear_combination (C A*X 0:Poly)*hr'+(X 1-C A*X 0)*hq'
  · simp [forward,backward,forwardVariables,inverseVariables,algebraMap_eq,map_mul]
    <;> linear_combination (C D*X 0:Poly)*hr'+(X 2-C D*X 0)*hqr'

/-- Actual algebra automorphism induced by the original triangular basis. -/
@[expose] def equivalence (q r A D : ℚ) (hq : q≠0) (hr : r≠0) : Poly ≃ₐ[ℚ] Poly :=
  AlgEquiv.ofAlgHom (forward q r A D) (backward q r A D)
    (forward_backward q r A D hq hr) (backward_forward q r A D hq hr)

/-- Rational relative primality survives this ACTUAL substitution. -/
theorem preserves_relPrime (q r A D : ℚ) (hq : q≠0) (hr : r≠0)
    (f g : Poly) (hfg : IsRelPrime f g) :
    IsRelPrime (forward q r A D f) (forward q r A D g) := by
  let e := equivalence q r A D hq hr
  change IsRelPrime (e f) (e g)
  apply IsRelPrime.of_map e.symm
  simpa only [AlgEquiv.symm_apply_apply] using hfg

/-- Evaluation after substitution is the actual rational basis map on the
same coordinate vector, not a convenient polynomial automorphism. -/
theorem forward_evaluation (q r A D : ℚ) (v : Fin 3 → ℚ) (f : Poly) :
    eval v (forward q r A D f)=
      eval (fun i : Fin 3 => if i=0 then r*v 0 else if i=1 then A*r*v 0+q*v 1
        else D*r*v 0+q*r*v 2) f := by
  have hh := comp_aeval_apply (f:=forwardVariables q r A D) (aeval v) f
  simpa [forward,forwardVariables,algebraMap_eq] using hh

end LiteralPolynomialBasisEquiv318
