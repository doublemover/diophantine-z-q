module
public import PELArithmeticRelativeGroupLaws318
public section
noncomputable section
namespace QuaternionicPositiveDeterminant318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicPeriodAutomorphy318
set_option maxHeartbeats 1400000

theorem denominator_nonzero (g : RealMatrices) (hg : 0<g.det) (τ : ℂ) (hτ : 0<τ.im) :
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
  exact (lt_irrefl 0) hg

/-- Positive determinant is retained as a multiplier; this is NOT the
old determinant-one identity silently applied to nonunits. -/
theorem mobius_im_det (g : RealMatrices) (τ : ℂ) :
    (mobius g τ).im=g.det*τ.im/Complex.normSq (denominator g τ) := by
  simp only [mobius,Complex.div_im,denominator,Complex.add_im,Complex.add_re,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
    zero_mul,add_zero,sub_zero]
  rw [←sub_div]
  congr 1
  rw [Matrix.det_fin_two]
  ring

theorem mobius_positive_det (g : RealMatrices) (hg : 0<g.det) (τ : ℂ) (hτ : 0<τ.im) :
    0<(mobius g τ).im := by
  rw [mobius_im_det]
  exact div_pos (mul_pos hg hτ) (Complex.normSq_pos.mpr (denominator_nonzero g hg τ hτ))

theorem mobius_comp_positive (g h : RealMatrices) (hg : 0<g.det) (hh : 0<h.det)
    (τ : ℂ) (hτ : 0<τ.im) : mobius g (mobius h τ)=mobius (g*h) τ := by
  have hd := denominator_nonzero h hh τ hτ
  have hg' := denominator_nonzero g hg (mobius h τ) (mobius_positive_det h hh τ hτ)
  have he := denominator_cocycle g h τ hd
  have hgh : denominator (g*h) τ≠0 := he ▸ mul_ne_zero hg' hd
  change numerator g (mobius h τ)/denominator g (mobius h τ)=
    numerator (g*h) τ/denominator (g*h) τ
  apply (div_eq_div_iff hg' hgh).mpr
  rw [←he,←numerator_cocycle g h τ hd]
  ring

/-- The SAME oriented original trace form scales by det(g), rather than
being preserved, under nonunit right multiplication. -/
theorem oriented_right_det (g M N : RealMatrices) :
    QuaternionicPeriodAlternating318.oriented (M*g) (N*g)=
      g.det*QuaternionicPeriodAlternating318.oriented M N := by
  unfold QuaternionicPeriodAlternating318.oriented QuaternionicPeriodAlternating318.pairing
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.det_fin_two]
  ring
end QuaternionicPositiveDeterminant318
