module
public import PELActualPolygonHomeomorph318
public import PELDirichletSidePairingData318
public section
noncomputable section
namespace PELOriginalKleinEquivariance318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELDirichletHeight318 PELQuaternionRealRepresentation318 PELQuaternionKleinAction318
set_option maxHeartbeats 1800000

@[expose] def upperNorm (M : RealMatrices) (τ : HalfPlane) : ℝ :=
  Complex.normSq ((M 0 0:ℂ)*(τ:ℂ)+(M 0 1:ℂ))
@[expose] def lowerNorm (M : RealMatrices) (τ : HalfPlane) : ℝ :=
  Complex.normSq (QuaternionicMobiusPeriods318.denominator M τ)
@[expose] def crossTerm (M : RealMatrices) (τ : HalfPlane) : ℝ :=
  (M 0 0*(τ:ℂ).re+M 0 1)*(M 1 0*(τ:ℂ).re+M 1 1)+
    M 0 0*M 1 0*(τ:ℂ).im^2
@[expose] def originalVector (M : RealMatrices) (τ : HalfPlane) : Fin 3 → ℝ :=
  realHomogeneous M *ᵥ ![scaledFirst τ,scaledSecond τ,1]

/-- All three homogeneous rows are the actual original complex numerator,
denominator and real cross term, including the precise Klein scale. -/
theorem vector_values (M : RealMatrices) (τ : HalfPlane) :
    originalVector M τ 0=alpha*beta*2*crossTerm M τ/(Complex.normSq (τ:ℂ)+1) ∧
    originalVector M τ 1=beta*(upperNorm M τ-lowerNorm M τ)/(Complex.normSq (τ:ℂ)+1) ∧
    originalVector M τ 2=(upperNorm M τ+lowerNorm M τ)/(Complex.normSq (τ:ℂ)+1) := by
  have hn : (τ:ℂ).re*(τ:ℂ).re+(τ:ℂ).im*(τ:ℂ).im+1≠0 := by
    nlinarith [sq_nonneg (τ:ℂ).re,sq_nonneg (τ:ℂ).im]
  constructor
  · simp only [originalVector,realHomogeneous,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one]
    unfold scaledFirst scaledSecond firstDisk secondDisk crossTerm
    simp only [Complex.normSq_apply]
    field_simp [hn] <;> ring
  · constructor
    · simp only [originalVector,realHomogeneous,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one]
      unfold scaledFirst scaledSecond firstDisk secondDisk upperNorm lowerNorm
      simp only [QuaternionicMobiusPeriods318.denominator,Complex.normSq_apply,
        Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,add_zero,zero_add,sub_zero]
      field_simp [hn,alpha_pos.ne'] <;> ring
    · simp only [originalVector,realHomogeneous,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one]
      unfold scaledFirst scaledSecond firstDisk secondDisk upperNorm lowerNorm
      simp only [QuaternionicMobiusPeriods318.denominator,Complex.normSq_apply,
        Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,add_zero,zero_add,sub_zero]
      field_simp [hn,alpha_pos.ne',beta_pos.ne'] <;> ring

@[expose] def matrixParameter (M : RealMatrices) (hM : M.det=1) (τ : HalfPlane) : HalfPlane :=
  ⟨mobius M τ,mobius_positive M hM τ τ.property⟩

theorem vector_denominator_positive (M : RealMatrices) (hM : M.det=1) (τ : HalfPlane) :
    0<originalVector M τ 2 := by
  rw [(vector_values M τ).2.2]
  apply div_pos
  · have hL : 0<lowerNorm M τ :=
      Complex.normSq_pos.mpr (QuaternionicMobiusPeriods318.denominator_ne M hM τ τ.property)
    have hU : 0≤upperNorm M τ := Complex.normSq_nonneg _
    linarith
  · nlinarith [Complex.normSq_nonneg (τ:ℂ)]

/-- Actual equivariance on EVERY real point of the original upper half-plane,
not only the rational endpoints listed by the arithmetic side certificate. -/
theorem original_scaled_action (M : RealMatrices) (hM : M.det=1) (τ : HalfPlane) :
    scaledFirst (matrixParameter M hM τ)=originalVector M τ 0/originalVector M τ 2 ∧
    scaledSecond (matrixParameter M hM τ)=originalVector M τ 1/originalVector M τ 2 := by
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hd : 0<lowerNorm M τ :=
    Complex.normSq_pos.mpr (QuaternionicMobiusPeriods318.denominator_ne M hM τ τ.property)
  have hs : upperNorm M τ+lowerNorm M τ≠0 := by
    have hU : 0≤upperNorm M τ := Complex.normSq_nonneg _
    linarith
  have hnorm : Complex.normSq (mobius M τ)=upperNorm M τ/lowerNorm M τ := by
    exact Complex.normSq_div _ _
  have hre : (mobius M τ).re=crossTerm M τ/lowerNorm M τ := by
    simp only [mobius,Complex.div_re,QuaternionicMobiusPeriods318.denominator,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,add_zero,zero_add,sub_zero,
      crossTerm,lowerNorm]
    ring
  constructor
  · change alpha*beta*(2*(mobius M τ).re/(Complex.normSq (mobius M τ)+1))=_
    rw [hre,hnorm,(vector_values M τ).1,(vector_values M τ).2.2]
    field_simp [hn,hd.ne',hs] <;> ring
  · change beta*((Complex.normSq (mobius M τ)-1)/(Complex.normSq (mobius M τ)+1))=_
    rw [hnorm,(vector_values M τ).2.1,(vector_values M τ).2.2]
    field_simp [hn,hd.ne',hs] <;> ring
end PELOriginalKleinEquivariance318
