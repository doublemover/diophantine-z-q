module
public import ActualGaussianWeberHenselianChart318
public section
noncomputable section

namespace ActualGaussianWeberFormalChord318

open IsLocalRing ActualGaussianWeberHenselianChart318

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A direct divided difference on the true origin chart, with
a unit denominator even on the diagonal. This is a polynomial
identity, not division by t₂-t₁. -/
theorem difference {t₁ t₂ w₁ w₂ : R}
    (h₁ : identityChart t₁ w₁) (h₂ : identityChart t₂ w₂) :
    (w₂-w₁)*(1+t₂*(w₂+w₁)) = (t₂-t₁)*(t₂^2+t₁*t₂+t₁^2-w₁^2) := by
  unfold identityChart at h₁ h₂
  linear_combination h₂ - h₁

/-- The coefficient order forced by the origin equation itself. -/
theorem cubic_order {t a w : R} (ht : t ∈ maximalIdeal R)
    (h : identityChart (t*a) w) : ∃ b : R, w=t^3*b := by
  have ht0 := (residue_eq_zero_iff t).mpr ht
  have hU : IsUnit (1+t*a*w) := (residue_ne_zero_iff_isUnit _).mp (by
    simp only [map_add,map_one,map_mul,ht0,zero_mul,add_zero,one_ne_zero])
  obtain ⟨u,hu⟩ := hU
  have he : w*(u:R)=(t*a)^3 := by
    rw [hu]
    unfold identityChart at h
    linear_combination h
  refine ⟨a^3*(↑u⁻¹:R),?_⟩
  apply u.isUnit.mul_right_cancel
  rw [he,mul_assoc,mul_assoc,u.inv_mul,mul_one,mul_pow]

/-- Substitute the line w=λt+ν in the literal projective chart.
Its leading coefficient is 1−λ² and the quadratic coefficient is
−2λν, establishing the precise sign in the third-root sum. -/
theorem line_polynomial (t l v : R) :
    t^3-((l*t+v)+t*(l*t+v)^2) =
      (1-l^2)*t^3-(2*l*v)*t^2-(l+v^2)*t-v := by ring

/-- Exact coefficient-order certificate for the same two-point chord.
If t₁,t₂ are multiples of t, the chord slope, intercept and third-root
correction are t²-, t³- and t⁵-multiples, including t=0.
The target group-law comparison is not hidden inside this statement. -/
theorem order_five (t a b w₁ w₂ : R) (ht : t ∈ maximalIdeal R)
    (h₁ : identityChart (t*a) w₁) (h₂ : identityChart (t*b) w₂) :
    ∃ l v C k : R,
      l*(1+(t*b)*(w₂+w₁))=(t*b)^2+(t*a)*(t*b)+(t*a)^2-w₁^2 ∧
      v=w₁-l*(t*a) ∧
      C*(1-l^2)=2*l*v ∧
      C=t^5*k := by
  have ht0 := (residue_eq_zero_iff t).mpr ht
  obtain ⟨u,hu⟩ : IsUnit (1+(t*b)*(w₂+w₁)) :=
    (residue_ne_zero_iff_isUnit _).mp (by
      simp only [map_add,map_one,map_mul,ht0,zero_mul,add_zero,one_ne_zero])
  obtain ⟨c,hc⟩ := cubic_order ht h₁
  let L : R := (b^2+a*b+a^2-t^4*c^2)*(↑u⁻¹:R)
  let V : R := c-L*a
  let l : R := t^2*L
  let v : R := t^3*V
  obtain ⟨d,hd⟩ : IsUnit (1-l^2) :=
    (residue_ne_zero_iff_isUnit _).mp (by
      simp only [l,map_sub,map_one,map_pow,map_mul,ht0,zero_pow (by decide : (2:ℕ) ≠ 0),
        zero_mul,sub_zero,one_ne_zero])
  let k : R := 2*L*V*(↑d⁻¹:R)
  refine ⟨l,v,t^5*k,k,?_,?_,?_,rfl⟩
  · rw [←hu]
    change (t^2*((b^2+a*b+a^2-t^4*c^2)*(↑u⁻¹:R)))*(u:R) = _
    rw [mul_assoc,mul_assoc,u.inv_mul,mul_one,hc]
    ring
  · change t^3*(c-L*a) = w₁-(t^2*L)*(t*a)
    rw [hc]
    ring
  · rw [←hd]
    change (t^5*(2*L*V*(↑d⁻¹:R)))*(d:R) = 2*(t^2*L)*(t^3*V)
    rw [mul_assoc,mul_assoc,d.inv_mul,mul_one]
    ring

end ActualGaussianWeberFormalChord318
