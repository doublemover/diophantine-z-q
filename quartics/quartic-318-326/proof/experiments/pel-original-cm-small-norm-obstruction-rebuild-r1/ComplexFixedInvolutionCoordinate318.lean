module
public import ComplexTwoPointCoordinate318
public section
noncomputable section
namespace ComplexFixedInvolutionCoordinate318
open ComplexTwoPointCoordinate318 QuaternionicRealPeriod318 QuaternionicMobiusPeriods318
open QuaternionicFixedParameter318
set_option maxHeartbeats 1800000

/-- A literal trace-zero fractional-linear map is negation in its actual
two-fixed-point coordinate, with all denominators explicitly retained. -/
theorem coordinate_negation (A B C D a b z : ℂ) (hab : a≠b)
    (ht : A+D=0) (ha : A*a+B=a*(C*a+D)) (hb : A*b+B=b*(C*b+D))
    (hz : z≠b) (hd : C*z+D≠0) (hf : (A*z+B)/(C*z+D)≠b) :
    coordinate a b ((A*z+B)/(C*z+D))= -coordinate a b z := by
  have hs0 : (a-b)*(C*(a+b)+2*D)=0 := by
    linear_combination -ha+hb+(a-b)*ht
  have hs : C*(a+b)+2*D=0 :=
    (mul_eq_zero.mp hs0).resolve_left (sub_ne_zero.mpr hab)
  have hp : B+C*a*b=0 := by
    linear_combination ha-a*ht+a*hs
  have hc : (A*z+B-a*(C*z+D))*(z-b)+
      (A*z+B-b*(C*z+D))*(z-a)=0 := by
    linear_combination (-a*z-b*z+2*z^2)*ht+(a*b-z^2)*hs+(-a-b+2*z)*hp
  unfold coordinate
  apply (div_eq_iff (sub_ne_zero.mpr hf)).mpr
  field_simp [hd,sub_ne_zero.mpr hz] <;> linear_combination hc

theorem upper_ne_conjugate (a z : ℂ) (ha : 0<a.im) (hz : 0<z.im) : z≠star a := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

theorem conjugate_fixes (M : RealMatrices) (a : ℂ) (ha : fixesLine M a) :
    fixesLine M (star a) := by
  have h := congrArg (starRingEnd ℂ) ha
  simpa [fixesLine] using h

/-- The actual upper-half-plane fixed-point chart sends the original
trace-zero Mobius action to minus its SAME coordinate at every upper point. -/
theorem original_negation (M : RealMatrices) (hM : 0<M.det) (a z : ℂ)
    (ha : 0<a.im) (hz : 0<z.im) (hfix : fixesLine M a) (ht : M 0 0+M 1 1=0) :
    coordinate a (star a) (mobius M z)= -coordinate a (star a) z := by
  have htC : (M 0 0:ℂ)+(M 1 1:ℂ)=0 := by exact_mod_cast ht
  have hden := QuaternionicPositiveDeterminant318.denominator_nonzero M hM z hz
  have him := QuaternionicPositiveDeterminant318.mobius_positive_det M hM z hz
  exact coordinate_negation _ _ _ _ a (star a) z
    (upper_ne_conjugate a a ha ha) htC hfix (conjugate_fixes M a hfix)
    (upper_ne_conjugate a z ha hz) hden (upper_ne_conjugate a (mobius M z) ha him)
end ComplexFixedInvolutionCoordinate318
