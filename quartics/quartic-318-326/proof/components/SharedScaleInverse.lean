module
public import QuarticOptimization
public section
namespace SharedScaleInverse
variable {K : Type*} [Field K]

theorem lambda_nonzero (lambda q : K) (F : K → K) (hF : F 0=0)
    (heq : q*F lambda=(lambda-1)^2) : lambda ≠ 0 := by
  intro h
  subst lambda
  simpa [hF] using heq

theorem equations (lambda mu A t d : K) (hi : mu*lambda=1) :
    (mu*t=A ∧ d=mu*(t^2-t)) ↔ (t=A*lambda ∧ d=A*(t-1)) := by
  have hm : mu ≠ 0 := by intro h; simp [h] at hi
  constructor
  · rintro ⟨ht,hd⟩
    constructor
    · calc
        t=(mu*lambda)*t := by rw [hi]; ring
        _=(mu*t)*lambda := by ring
        _=A*lambda := by rw [ht]
    · calc
        d=mu*(t^2-t) := hd
        _=(mu*t)*(t-1) := by ring
        _=A*(t-1) := by rw [ht]
  · rintro ⟨ht,hd⟩
    constructor
    · rw [ht]
      calc
        mu*(A*lambda)=A*(mu*lambda) := by ring
        _=A := by rw [hi]; ring
    · have hh : mu*t=A := by rw [ht]; calc
        mu*(A*lambda)=A*(mu*lambda) := by ring
        _=A := by rw [hi]; ring
      rw [hd]
      calc
        A*(t-1)=(mu*t)*(t-1) := by rw [hh]
        _=mu*(t^2-t) := by ring

theorem inverse_exists (lambda : K) (hl : lambda ≠ 0) :
    ∃ mu : K, mu*lambda=1 := ⟨lambda⁻¹,inv_mul_cancel₀ hl⟩

end SharedScaleInverse
