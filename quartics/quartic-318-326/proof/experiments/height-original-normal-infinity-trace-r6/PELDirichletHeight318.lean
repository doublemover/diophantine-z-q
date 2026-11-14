module
public import PELDirichletOriginalUnits318
public section
noncomputable section
namespace PELDirichletHeight318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318 QuaternionicMobiusPeriods318
open PELQuaternionAlgebra318 PELQuaternionRealRepresentation318 PELJointNormOneAction318
open PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
set_option maxHeartbeats 1800000

@[expose] def height (τ : HalfPlane) : ℝ := (Complex.normSq (τ:ℂ)+1)/(τ:ℂ).im
/-- Auxiliary REAL Klein disk coordinates, not a replacement complex chart. -/
@[expose] def firstDisk (τ : HalfPlane) : ℝ := 2*(τ:ℂ).re/(Complex.normSq (τ:ℂ)+1)
@[expose] def secondDisk (τ : HalfPlane) : ℝ := (Complex.normSq (τ:ℂ)-1)/(Complex.normSq (τ:ℂ)+1)
@[expose] def scaledFirst (τ : HalfPlane) : ℝ := alpha*beta*firstDisk τ
@[expose] def scaledSecond (τ : HalfPlane) : ℝ := beta*secondDisk τ

theorem height_pos (τ : HalfPlane) : 0<height τ :=
  div_pos (by nlinarith [Complex.normSq_nonneg (τ:ℂ)]) τ.property

theorem disk_height_identity (τ : HalfPlane) :
    (1-(scaledFirst τ)^2/1050-(scaledSecond τ)^2/5)*(height τ)^2=4 := by
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  unfold height scaledFirst scaledSecond firstDisk secondDisk
  field_simp [hn,τ.property.ne']
  simp only [Complex.normSq_apply]
  ring_nf <;> simp only [alpha_sq,beta_sq] <;> ring

theorem mobius_height (M : RealMatrices) (hM : M.det=1) (τ : HalfPlane) :
    (Complex.normSq (mobius M τ)+1)/(mobius M τ).im=
      (Complex.normSq ((M 0 0:ℂ)*(τ:ℂ)+(M 0 1:ℂ))+
       Complex.normSq (denominator M τ))/(τ:ℂ).im := by
  have hd := Complex.normSq_pos.mpr (denominator_ne M hM τ τ.property)
  rw [mobius_im M hM]
  simp only [mobius,Complex.normSq_div]
  field_simp [hd.ne',τ.property.ne'] <;> ring

/-- Exact energy transformation for the original SL2 action, retaining
both numerator and denominator rows of its matrix. -/
theorem matrix_energy (M : RealMatrices) (hM : M.det=1) (τ : HalfPlane) :
    2*((Complex.normSq (mobius M τ)+1)/(mobius M τ).im-height τ)/height τ=
      (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2-2)+
      2*(M 0 0*M 0 1+M 1 0*M 1 1)*firstDisk τ+
      (M 0 0^2+M 1 0^2-M 0 1^2-M 1 1^2)*secondDisk τ := by
  rw [mobius_height M hM]
  have hn : Complex.normSq (τ:ℂ)+1≠0 := by nlinarith [Complex.normSq_nonneg (τ:ℂ)]
  have hn' : (τ:ℂ).re*(τ:ℂ).re+(τ:ℂ).im*(τ:ℂ).im+1≠0 := by
    simpa only [Complex.normSq_apply] using hn
  unfold height firstDisk secondDisk
  simp only [denominator,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    mul_zero,sub_zero,add_zero,zero_add]
  field_simp [hn',τ.property.ne'] <;> ring

/-- The finite test units act through their literal original quaternion
representation; all real energy coefficients are the exact rational rows. -/
theorem original_energy (j : Fin 8) (ε δ : Bool) (τ : HalfPlane) :
    2*(height (testUnit j ε δ • τ)-height τ)/height τ=
      (rowConstant j:ℝ)-(rowFirst j:ℝ)*(sign ε:ℝ)*scaledFirst τ-
      (rowSecond j:ℝ)*(sign δ:ℝ)*scaledSecond τ := by
  let q := embed (signedCoefficients j ε δ)
  have hq : reducedNorm q=1 := by
    rw [embed_norm,signed_norm] <;> norm_num
  have hdet : (representation q).det=1 := by
    rw [PELPeriodDeterminant318.representation_det,hq] <;> norm_num
  have h := matrix_energy (representation q) hdet τ
  change 2*((Complex.normSq (mobius (representation q) τ)+1)/
      (mobius (representation q) τ).im-height τ)/height τ=_
  rw [h]
  obtain ⟨hc,hu,hv⟩ := energy_coefficients j ε δ
  have hc' := congrArg (fun x : ℚ => (x:ℝ)) hc
  have hu' := congrArg (fun x : ℚ => (x:ℝ)) hu
  have hv' := congrArg (fun x : ℚ => (x:ℝ)) hv
  push_cast at hc' hu' hv'
  change (((q.re:ℝ)+beta*(q.imJ:ℝ))^2+(-alpha*(q.imI:ℝ)+alpha*beta*(q.imK:ℝ))^2+
    (alpha*(q.imI:ℝ)+alpha*beta*(q.imK:ℝ))^2+((q.re:ℝ)-beta*(q.imJ:ℝ))^2-2)+
    2*(((q.re:ℝ)+beta*(q.imJ:ℝ))*(-alpha*(q.imI:ℝ)+alpha*beta*(q.imK:ℝ))+
      (alpha*(q.imI:ℝ)+alpha*beta*(q.imK:ℝ))*((q.re:ℝ)-beta*(q.imJ:ℝ)))*firstDisk τ+
    (((q.re:ℝ)+beta*(q.imJ:ℝ))^2+(alpha*(q.imI:ℝ)+alpha*beta*(q.imK:ℝ))^2-
      (-alpha*(q.imI:ℝ)+alpha*beta*(q.imK:ℝ))^2-((q.re:ℝ)-beta*(q.imJ:ℝ))^2)*secondDisk τ=_
  unfold scaledFirst scaledSecond
  ring_nf <;> simp only [alpha_sq,beta_sq] <;>
    linear_combination hc'+alpha*beta*firstDisk τ*hu'+beta*secondDisk τ*hv'
end PELDirichletHeight318
