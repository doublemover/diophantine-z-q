module
public import Mathlib.Tactic
public section
namespace ActualLinearQTwoNormInject318

/-- Exact linear forms before any Gaussian lift or absolute value.
The additional q form is the sole occurrence of none. -/
@[expose] def atForm (Q : ℤ) (u q : ℤ) : Option ℤ → ℤ
  | none => q
  | some k => u+k*Q^2*q

/-- Two genuinely different merged positions determine the SAME key.
For equal positions the theorem deliberately does not apply, so the
diagonal event must be charged using a distinct companion. -/
theorem two_forms (Q u q v r : ℤ) (hQ : Q ≠ 0) (i j : Option ℤ) (hij : i ≠ j)
    (h₁ : atForm Q u q i = atForm Q v r i)
    (h₂ : atForm Q u q j = atForm Q v r j) :
    u=v ∧ q=r := by
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some j =>
      change q=r at h₁
      change u+j*Q^2*q=v+j*Q^2*r at h₂
      exact ⟨by rw [h₁] at h₂; linarith only [h₂],h₁⟩
  | some i =>
    cases j with
    | none =>
      change q=r at h₂
      change u+i*Q^2*q=v+i*Q^2*r at h₁
      exact ⟨by rw [h₂] at h₁; linarith only [h₁],h₂⟩
    | some j =>
      change u+i*Q^2*q=v+i*Q^2*r at h₁
      change u+j*Q^2*q=v+j*Q^2*r at h₂
      have hn : i-j ≠ 0 := sub_ne_zero.mpr (fun e => hij (congrArg some e))
      have H : ((i-j)*Q^2)*(q-r)=0 := by linear_combination h₁ - h₂
      have hqr : q=r := sub_eq_zero.mp
        ((mul_eq_zero.mp H).resolve_left (mul_ne_zero hn (pow_ne_zero 2 hQ)))
      exact ⟨by rw [hqr] at h₁; linarith only [h₁],hqr⟩

end ActualLinearQTwoNormInject318
