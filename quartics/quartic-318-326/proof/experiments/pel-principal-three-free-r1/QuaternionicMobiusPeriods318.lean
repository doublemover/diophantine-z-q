module
public import QuaternionicPeriodAlternating318
public section
noncomputable section
namespace QuaternionicMobiusPeriods318
open QuaternionicRealPeriod318
set_option maxHeartbeats 1000000
@[expose] def denominator (g : RealMatrices) (τ : ℂ) : ℂ := (g 1 0:ℂ)*τ+(g 1 1:ℂ)
@[expose] def mobius (g : RealMatrices) (τ : ℂ) : ℂ :=
  ((g 0 0:ℂ)*τ+(g 0 1:ℂ))/denominator g τ

/-- The actual lower row cannot vanish in the upper half-plane. -/
theorem denominator_ne (g : RealMatrices) (hg : g.det=1) (τ : ℂ) (hτ : 0<τ.im) :
    denominator g τ≠0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp only [denominator,Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,sub_zero,Complex.zero_im,
    Complex.zero_re] at hi hr
  have hc : g 1 0=0 := (mul_eq_zero.mp hi).resolve_right hτ.ne'
  simp only [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hg
  simp only [hc,zero_mul,zero_add] at hr
  rw [hr,mul_zero] at hg
  norm_num at hg

theorem mobius_im (g : RealMatrices) (hg : g.det=1) (τ : ℂ) :
    (mobius g τ).im=τ.im/Complex.normSq (denominator g τ) := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using hg
  simp only [mobius,Complex.div_im,denominator,Complex.add_im,Complex.add_re,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
    zero_mul,add_zero,sub_zero]
  rw [←sub_div]
  congr 1
  linear_combination τ.im*hd

theorem mobius_positive (g : RealMatrices) (hg : g.det=1) (τ : ℂ) (hτ : 0<τ.im) :
    0<(mobius g τ).im := by
  rw [mobius_im g hg]
  exact div_pos hτ (Complex.normSq_pos.mpr (denominator_ne g hg τ hτ))

/-- Right multiplication, not the original left order action, supplies the
arithmetic base change of period fibers. The automorphy scalar is retained. -/
theorem period_mobius (g M : RealMatrices) (τ : ℂ) (hd : denominator g τ≠0) :
    period (mobius g τ) M=(denominator g τ)⁻¹ • period τ (M*g) := by
  funext i
  simp only [period,row,LinearMap.coe_mk,AddHom.coe_mk,mobius,Matrix.mul_apply,
    Fin.sum_univ_two,Complex.ofReal_add,Complex.ofReal_mul,Pi.smul_apply,smul_eq_mul]
  field_simp [hd]
  unfold denominator
  ring

/-- Both orientations of the fixed trace form are preserved by determinant
one RIGHT multiplication; no sign change is hidden in the transition. -/
theorem oriented_right (g M N : RealMatrices) (hg : g.det=1) :
    QuaternionicPeriodAlternating318.oriented (M*g) (N*g)=
      QuaternionicPeriodAlternating318.oriented M N := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using hg
  unfold QuaternionicPeriodAlternating318.oriented QuaternionicPeriodAlternating318.pairing
  congr 1
  congr 1
  simp only [Matrix.mul_apply,Fin.sum_univ_two]
  linear_combination
    (M 0 0*N 0 1-M 0 1*N 0 0+M 1 0*N 1 1-M 1 1*N 1 0)*hd
end QuaternionicMobiusPeriods318
