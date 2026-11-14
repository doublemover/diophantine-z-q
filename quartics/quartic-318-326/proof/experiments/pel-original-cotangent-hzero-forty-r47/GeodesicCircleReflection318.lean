module
public import GeodesicCircleFlattening318
public import Mathlib.Analysis.Calculus.Deriv.Star
public section
noncomputable section
namespace GeodesicCircleReflection318
open Complex Set
open scoped ComplexConjugate
set_option maxHeartbeats 2800000

/-- The positive-determinant real Mobius map obtained by composing
reflection in the actual semicircle with the original mirror z↦−conj z. -/
@[expose] def circleMobius (a b:ℝ) (z:ℂ) : ℂ :=
  (-(a+b:ℝ)*z+2*(a:ℂ)*b)/(2*z-(a+b:ℝ))
@[expose] def circleReflection (a b:ℝ) (z:ℂ) : ℂ := -conj (circleMobius a b z)

theorem denominator_ne (a b:ℝ) (z:ℂ) (hz:0<z.im) : 2*z-(a+b:ℝ)≠0 := by
  intro he
  have hi:=congrArg Complex.im he
  simp only [Complex.sub_im,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
    Complex.ofReal_im,mul_zero,zero_mul,zero_add,sub_zero,Complex.zero_im] at hi
  linarith

theorem circleMobius_im (a b:ℝ) (z:ℂ) :
    (circleMobius a b z).im=(b-a)^2*z.im/normSq (2*z-(a+b:ℝ)) := by
  simp only [circleMobius,Complex.div_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem circleMobius_positive (a b:ℝ) (hab:a<b) (z:ℂ) (hz:0<z.im) :
    0<(circleMobius a b z).im := by
  rw [circleMobius_im]
  exact div_pos (mul_pos (sq_pos_of_pos (sub_pos.mpr hab)) hz)
    (normSq_pos.mpr (denominator_ne a b z hz))

theorem circleReflection_positive (a b:ℝ) (hab:a<b) (z:ℂ) (hz:0<z.im) :
    0<(circleReflection a b z).im := by
  simpa only [circleReflection,Complex.neg_im,Complex.conj_im,neg_neg] using
    circleMobius_positive a b hab z hz

/-- Genuine reflection in the original geodesic is the chart-conjugated
ordinary conjugation. The identity holds on the WHOLE upper half-plane,
not just on the semicircle boundary. -/
theorem inverse_conjugate_flatten (a b:ℝ) (z:ℂ) (hz:0<z.im) :
    GeodesicCircleFlattening318.unflatten a b
      (conj (GeodesicCircleFlattening318.flatten a b z))=circleReflection a b z := by
  have hb:(b:ℂ)-conj z≠0 := by
    intro he
    have hh:=congrArg (conj:ℂ→ℂ) he
    exact GeodesicCircleFlattening318.endpoint_ne b z hz (by simpa using hh)
  have hd:2*conj z-(a+b:ℝ)≠0 := by
    intro he
    have hh:=congrArg (conj:ℂ→ℂ) he
    exact denominator_ne a b z hz (by simpa using hh)
  have hd':(a+b:ℝ)-2*conj z≠0 := by
    intro he
    apply hd
    linear_combination -he
  have hcf:conj (GeodesicCircleFlattening318.flatten a b z)=
      Complex.I*((conj z-a)/((b:ℂ)-conj z)) := by
    simp [GeodesicCircleFlattening318.flatten]
  have hn:(a:ℂ)+(b:ℂ)*(Complex.I*(conj (GeodesicCircleFlattening318.flatten a b z)))=
      (2*(a:ℂ)*b-(a+b:ℝ)*conj z)/((b:ℂ)-conj z) := by
    rw [hcf]
    push_cast
    field_simp [hb]
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hh:1+Complex.I*(conj (GeodesicCircleFlattening318.flatten a b z))=
      ((a+b:ℝ)-2*conj z)/((b:ℂ)-conj z) := by
    rw [hcf]
    push_cast
    field_simp [hb]
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold GeodesicCircleFlattening318.unflatten
  rw [hn,hh]
  simp only [circleReflection,circleMobius,map_div,map_sub,map_mul,map_neg,
    map_ofNat,Complex.conj_ofReal]
  push_cast
  field_simp [hb,hd,hd']
  ring

/-- The actual finite Joukowski coordinate is unchanged when the
original mirror-side value is replaced by the reciprocal Schwarz value.
This is an identity on a whole collar, not just on its unit-circle seam. -/
theorem joukowski_mirror_reciprocal (w:ℂ) :
    (-conj w)-(-conj w)⁻¹=(conj w)⁻¹-((conj w)⁻¹)⁻¹ := by
  simp only [inv_neg,inv_inv]
  ring
end GeodesicCircleReflection318
