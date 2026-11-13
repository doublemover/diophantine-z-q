module
public import QuaternionicMobiusPeriods318
public section
noncomputable section
namespace QuaternionicFixedParameter318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318
set_option maxHeartbeats 1200000
/-- Preservation of the original complex line C(τ,1), without dividing by
a possibly zero denominator for nonunits. -/
@[expose] def fixesLine (M : RealMatrices) (τ : ℂ) : Prop :=
  (M 0 0:ℂ)*τ+(M 0 1:ℂ)=τ*((M 1 0:ℂ)*τ+(M 1 1:ℂ))

theorem fixesLine_of_mobius (M : RealMatrices) (τ : ℂ)
    (hd : denominator M τ≠0) (h : mobius M τ=τ) : fixesLine M τ :=
  (div_eq_iff hd).mp h

theorem coordinate_relations (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (h : fixesLine M τ) :
    M 0 0=M 1 1+2*M 1 0*τ.re ∧ M 0 1= -M 1 0*(τ.re^2+τ.im^2) := by
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp only [Complex.add_im,Complex.add_re,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,sub_zero] at hi hr
  have he : (M 0 0-M 1 1-2*M 1 0*τ.re)*τ.im=0 := by nlinarith [hi]
  have ha : M 0 0=M 1 1+2*M 1 0*τ.re := by
    have hz := (mul_eq_zero.mp he).resolve_right hτ.ne'
    linarith
  refine ⟨ha,?_⟩
  rw [ha] at hr
  nlinarith [hr]

theorem determinant_squares (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (h : fixesLine M τ) :
    M.det=(M 1 1+M 1 0*τ.re)^2+(M 1 0*τ.im)^2 := by
  obtain ⟨ha,hb⟩ := coordinate_relations M τ hτ h
  rw [Matrix.det_fin_two,ha,hb]
  ring

theorem trace_bound (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (h : fixesLine M τ) : (M 0 0+M 1 1)^2≤4*M.det := by
  obtain ⟨ha,hb⟩ := coordinate_relations M τ hτ h
  rw [determinant_squares M τ hτ h,ha]
  nlinarith [sq_nonneg (M 1 0*τ.im)]

theorem zero_of_det_zero (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (h : fixesLine M τ) (hd : M.det=0) : M=0 := by
  have hs := determinant_squares M τ hτ h
  rw [hd] at hs
  have hc : M 1 0*τ.im=0 := by nlinarith [sq_nonneg (M 1 1+M 1 0*τ.re)]
  have hc0 : M 1 0=0 := (mul_eq_zero.mp hc).resolve_right hτ.ne'
  have hd0 : M 1 1=0 := by rw [hc0] at hs; nlinarith
  obtain ⟨ha,hb⟩ := coordinate_relations M τ hτ h
  have ha0 : M 0 0=0 := by simpa only [hc0,hd0,mul_zero,zero_mul,add_zero] using ha
  have hb0 : M 0 1=0 := by simpa only [hc0,neg_zero,zero_mul] using hb
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha0,hb0,hc0,hd0]

/-- Removing the scalar identity and the exact principal-three coefficient
preserves the same complex line. -/
theorem remove_identity_three (M : RealMatrices) (τ : ℂ)
    (h : fixesLine (1+(3:ℕ) • M) τ) : fixesLine M τ := by
  have hentry (i j:Fin 2) : ((3:ℕ) • M) i j=3*M i j := by
    change (3:ℕ) • (M i j)=3*M i j
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have h' : ((1+3*M 0 0:ℝ):ℂ)*τ+(3*M 0 1:ℝ)=
      τ*((3*M 1 0:ℝ)*τ+(1+3*M 1 1:ℝ)) := by
    simp only [fixesLine, Matrix.add_apply, hentry] at h
    simpa using h
  push_cast at h'
  unfold fixesLine
  linear_combination (1/3:ℂ)*h'
end QuaternionicFixedParameter318
