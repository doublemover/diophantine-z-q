module
public import ActualGaussianWeberFormalChord318
public section
noncomputable section

namespace ActualGaussianWeberOriginVieta318

open ActualGaussianWeberHenselianChart318 ActualGaussianWeberFormalChord318

variable {R : Type*} [CommRing R]

@[expose] def thirdT (t₁ t₂ C : R) : R := C-t₁-t₂

@[expose] def thirdW (t₁ t₂ l v C : R) : R := l*thirdT t₁ t₂ C+v

structure ScaledVieta (t₁ w₁ t₂ w₂ l v C : R) : Prop where
  line₁ : w₁=l*t₁+v
  line₂ : w₂=l*t₂+v
  s₁ : (1-l^2)*(t₁+t₂+thirdT t₁ t₂ C)=2*l*v
  s₂ : (1-l^2)*(t₁*t₂+(t₁+t₂)*thirdT t₁ t₂ C)= -(l+v^2)
  s₃ : (1-l^2)*t₁*t₂*thirdT t₁ t₂ C=v
  third_chart : identityChart (thirdT t₁ t₂ C) (thirdW t₁ t₂ l v C)

/-- Divided difference remains valid at equal abscissae, so there is no
assumption of distinct roots hidden in Vieta or in the third chart. -/
theorem scaled_vieta {t₁ w₁ t₂ w₂ l v C : R}
    (h₁ : identityChart t₁ w₁) (h₂ : identityChart t₂ w₂)
    (hU : IsUnit (1+t₂*(w₂+w₁)))
    (hl : l*(1+t₂*(w₂+w₁))=t₂^2+t₁*t₂+t₁^2-w₁^2)
    (hv : v=w₁-l*t₁) (hC : C*(1-l^2)=2*l*v) :
    ScaledVieta t₁ w₁ t₂ w₂ l v C := by
  have hL₁ : w₁=l*t₁+v := by linear_combination -hv
  have hAux := difference h₁ h₂
  have hdiff : w₂-w₁=l*(t₂-t₁) := by
    apply hU.mul_right_cancel
    linear_combination hAux - (t₂-t₁)*hl
  have hL₂ : w₂=l*t₂+v := by linear_combination hdiff + hL₁
  have hd : (1-l^2)*(t₁^2+t₁*t₂+t₂^2)-2*l*v*(t₁+t₂)-(l+v^2)=0 := by
    rw [hL₁,hL₂] at hl
    linear_combination -hl
  have hp : (1-l^2)*t₁^3-(2*l*v)*t₁^2-(l+v^2)*t₁-v=0 := by
    rw [←line_polynomial,←hL₁]
    unfold identityChart at h₁
    rw [h₁,sub_self]
  have hS₁ : (1-l^2)*(t₁+t₂+thirdT t₁ t₂ C)=2*l*v := by
    unfold thirdT
    linear_combination hC
  have hS₂ : (1-l^2)*(t₁*t₂+(t₁+t₂)*thirdT t₁ t₂ C)= -(l+v^2) := by
    unfold thirdT
    linear_combination (t₁+t₂)*hC - hd
  have hS₃ : (1-l^2)*t₁*t₂*thirdT t₁ t₂ C=v := by
    unfold thirdT
    linear_combination (t₁*t₂)*hC + hp - t₁*hd
  refine ⟨hL₁,hL₂,hS₁,hS₂,hS₃,?_⟩
  let T := thirdT t₁ t₂ C
  have hfactor (s : R) :
      (1-l^2)*s^3-(2*l*v)*s^2-(l+v^2)*s-v =
        (1-l^2)*(s-t₁)*(s-t₂)*(s-T) := by
    change _ = (1-l^2)*(s-t₁)*(s-t₂)*(s-thirdT t₁ t₂ C)
    linear_combination s^2*hS₁ - s*hS₂ + hS₃
  have hft := hfactor T
  rw [sub_self,mul_zero] at hft
  change identityChart T (l*T+v)
  unfold identityChart
  exact (sub_eq_zero.mp ((line_polynomial T l v).trans hft)).symm

theorem weighted_denominator {t₁ w₁ t₂ w₂ l v C : R}
    (h : ScaledVieta t₁ w₁ t₂ w₂ l v C) :
    (1-l^2)*w₁*w₂*thirdW t₁ t₂ l v C=v^3 := by
  rw [h.line₁,h.line₂]
  unfold thirdW
  linear_combination l^3*h.s₃ + (l^2*v)*h.s₂ + (l*v^2)*h.s₁

theorem weighted_numerator {t₁ w₁ t₂ w₂ l v C : R}
    (h : ScaledVieta t₁ w₁ t₂ w₂ l v C) :
    (1-l^2)*(t₁*w₂*thirdW t₁ t₂ l v C + t₂*w₁*thirdW t₁ t₂ l v C
      + thirdT t₁ t₂ C*w₁*w₂)=l^2*v := by
  rw [h.line₁,h.line₂]
  unfold thirdW
  linear_combination (3*l^2)*h.s₃ + (2*l*v)*h.s₂ + v^2*h.s₁

theorem tangent_denominator {t w l v : R} (h : identityChart t w)
    (hl : l*(1+t*(w+w))=t^2+t*t+t^2-w^2) (hv : v=w-l*t) :
    v*(1+2*t*w) = -2*w := by
  rw [hv]
  unfold identityChart at h
  linear_combination -t*hl + 3*h

section Field
variable {F : Type*} [Field F]

/-- Computed sum of the three original affine abscissae after the literal
chart-to-affine coordinate conversion. The nonvertical chart slope is l/v. -/
theorem affine_abscissa_sum {t₁ w₁ t₂ w₂ l v C : F}
    (h : ScaledVieta t₁ w₁ t₂ w₂ l v C) (hv : v ≠ 0) (h₁ : w₁ ≠ 0) (h₂ : w₂ ≠ 0) :
    w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ thirdW t₁ t₂ l v C ≠ 0 ∧
      t₁/w₁+t₂/w₂+thirdT t₁ t₂ C/thirdW t₁ t₂ l v C=(l/v)^2 := by
  let T := thirdT t₁ t₂ C
  let W := thirdW t₁ t₂ l v C
  have hd : (1-l^2)*w₁*w₂*W=v^3 := weighted_denominator h
  have hn : (1-l^2)*(t₁*w₂*W+t₂*w₁*W+T*w₁*w₂)=l^2*v := weighted_numerator h
  have hW : W ≠ 0 := by
    intro H
    exact (pow_ne_zero 3 hv) (by simpa only [H,mul_zero] using hd.symm)
  have hU : 1-l^2 ≠ 0 := by
    intro H
    exact (pow_ne_zero 3 hv) (by simpa only [H,zero_mul] using hd.symm)
  refine ⟨h₁,h₂,hW,?_⟩
  change t₁/w₁+t₂/w₂+T/W=(l/v)^2
  have hEq : t₁/w₁+t₂/w₂+T/W =
      (t₁*w₂*W+t₂*w₁*W+T*w₁*w₂)/(w₁*w₂*W) := by
    field_simp [h₁,h₂,hW] <;> ring
  rw [hEq,div_pow]
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero h₁ h₂) hW) (pow_ne_zero 2 hv)).mpr
  apply mul_left_cancel₀ hU
  linear_combination v^2*hn - l^2*hd

end Field

end ActualGaussianWeberOriginVieta318
