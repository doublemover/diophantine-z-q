module
public import ActualGaussianWeberHenselianChart318
public section
noncomputable section

namespace ActualGaussianWeberMixedPolynomial318

open ActualGaussianWeberHenselianChart318

variable {R : Type*} [CommRing R]

@[expose] def H (t w A B : R) : R := 2*B+(3*A^2-1)*t-(A^3+A)*w

/-- Exact numerator before any divisions. D=t−Aw is the numerator
of the original difference of abscissae, not a residue denominator. -/
theorem cleared_numerator {t w A B : R} (h₀ : identityChart t w)
    (hQ : B^2=A^3-A) :
    w*(1+B*w)^2-(t+2*A*w)*(t-A*w)^2=w^2*H t w A B := by
  unfold H
  unfold identityChart at h₀
  linear_combination h₀+w^3*hQ

section Field
variable {F : Type*} [Field F]

theorem unscaled_slope_square {t w A B : F} (h₀ : identityChart t w)
    (hQ : B^2=A^3-A) (hw : w ≠ 0) (hd : t-A*w ≠ 0) :
    (-(1+B*w)/(t-A*w))^2-t/w-2*A =
      (w/(t-A*w)^2)*H t w A B := by
  apply mul_right_cancel₀ (mul_ne_zero hw (pow_ne_zero 2 hd))
  calc
    _ = w*(1+B*w)^2-(t+2*A*w)*(t-A*w)^2 := by
      field_simp [hw,hd] <;> ring
    _ = w^2*H t w A B := cleared_numerator h₀ hQ
    _ = _ := by field_simp [hd] <;> ring

theorem scaled_factor {t w A u beta : F} (hW : w=t^3*u)
    (hD : (t-A*w)*beta=t) (hd : t-A*w ≠ 0) :
    w/(t-A*w)^2=t*u*beta^2 := by
  apply (div_eq_iff (pow_ne_zero 2 hd)).mpr
  calc
    w = t^3*u := hW
    _ = t*u*t^2 := by ring
    _ = t*u*((t-A*w)*beta)^2 := by rw [hD]
    _ = _ := by ring

/-- The square formula and the exact cancellation at the reflected y.
The right sides are products of integral factors when t,w are small. -/
theorem scaled_chord {t w A B u beta : F} (h₀ : identityChart t w)
    (hQ : B^2=A^3-A) (ht : t ≠ 0) (hw : w ≠ 0)
    (hW : w=t^3*u) (hD : (t-A*w)*beta=t) :
    t-A*w ≠ 0 ∧
    (-(1+B*w)/(t-A*w))^2-t/w-2*A = t*u*beta^2*H t w A B ∧
    ((1+B*w)/(t-A*w))*(t*u*beta^2*H t w A B) =
       (1+B*w)*u*beta^3*H t w A B := by
  have hd : t-A*w ≠ 0 := by
    intro H0
    apply ht
    rw [H0,zero_mul] at hD
    exact hD.symm
  refine ⟨hd,?_,?_⟩
  · rw [unscaled_slope_square h₀ hQ hw hd,scaled_factor hW hD hd]
  · apply mul_left_cancel₀ hd
    calc
      _ = (1+B*w)*(t*u*beta^2*H t w A B) := by
        field_simp [hd] <;> ring
      _ = (1+B*w)*(((t-A*w)*beta)*u*beta^2*H t w A B) := by rw [hD]
      _ = _ := by ring

end Field

end ActualGaussianWeberMixedPolynomial318
