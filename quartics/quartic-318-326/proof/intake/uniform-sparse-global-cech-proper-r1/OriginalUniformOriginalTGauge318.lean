module
public import OriginalUniformMarkedMatrices318
public section
namespace OriginalUniformOriginalTGauge318
open OriginalUniformMarkedQMSurface318 OriginalMarkedIntPolynomialCertificate318 OriginalUniformCowanData318
open OriginalPhysicalNaganoFirstJet318 OriginalUniformCowanDerivative318 OriginalScalarExceptionalMap318
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]
@[expose] def c32 (z : K) := z^2-z-1
@[expose] def c343 (z : K) := z^2+4*z-1
@[expose] def c0 (z : K) := 1+z^2
theorem contact32 (z : K) : horner z regTNum-32*horner z regTDen=9600*(c32 z)^2 := by
  simp [regTNum,regTDen,nn,dd,horner,c32]; ring
theorem contact343 (z : K) : horner z regTNum+343*horner z regTDen=25725*(c343 z)^2 := by
  simp [regTNum,regTDen,nn,dd,horner,c343]; ring
theorem contact76832 (z : K) : horner z regTNum-76832*horner z regTDen= -3292800*(row z).X := by
  change horner z nn-76832*horner z dd= -3292800*(horner z regXNum/horner z regXDen)
  simp [regXNum,regXDen,nn,dd,horner]; ring
theorem wronskian (z : K) :
    dH z regTNum*horner z regTDen-horner z regTNum*dH z regTDen=6585600*c0 z*c32 z*c343 z := by
  simp only [eval_derivative,OriginalPhysicalNaganoReadback318.h]
  simp [regTNum,regTDen,nn,dd,horner,dcoeff,mulIdx,c0,c32,c343]
  ring
theorem y_den (z : K) : (row z).Y=horner z regTDen := by
  change horner z dd/horner z ([1]:List ℤ)=horner z dd
  simp [horner]
structure Result [CharZero K] (d : Row K) (z R : K) : Prop where
  tangent_ne : quotientJet z regTNum regTDen≠0
  contact_ne : (d.T-32)*(d.T+343)*(d.T-76832)≠0
  algebraic : (c0 z)^2*normalizedKS d R =
    (189000/((d.T-32)*(d.T+343)*(d.T-76832)))*(quotientJet z regTNum regTDen)^2
  theta_scaled : (5/4)*(c0 z)^2*normalizedKS d R =
    (236250/((d.T-32)*(d.T+343)*(d.T-76832)))*(quotientJet z regTNum regTDen)^2
theorem of_units [CharZero K] (z R : K) (hD : horner z regTDen≠0) (hX : (row z).X≠0)
    (h0 : c0 z≠0) (h32 : c32 z≠0) (h343 : c343 z≠0)
    (hk : normalizedKS (row z) R= -10080/((row z).X*(row z).Y)) : Result (row z) z R := by
  let Y := horner z regTDen
  have f32 : ((row z).T-32)*Y=9600*(c32 z)^2 := by
    change (horner z regTNum/horner z regTDen-32)*horner z regTDen=_
    field_simp
    linear_combination contact32 z
  have f343 : ((row z).T+343)*Y=25725*(c343 z)^2 := by
    change (horner z regTNum/horner z regTDen+343)*horner z regTDen=_
    field_simp
    linear_combination contact343 z
  have fx : ((row z).T-76832)*Y= -3292800*(row z).X := by
    change (horner z regTNum/horner z regTDen-76832)*horner z regTDen=_
    field_simp
    linear_combination contact76832 z
  have nj : quotientJet z regTNum regTDen*Y^2=6585600*c0 z*c32 z*c343 z := by
    unfold quotientJet
    rw [wronskian]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hD)
  have cf32 := left_ne_zero_of_mul (f32 ▸ mul_ne_zero (by norm_num : (9600:K)≠0) (pow_ne_zero 2 h32))
  have cf343 := left_ne_zero_of_mul (f343 ▸ mul_ne_zero (by norm_num : (25725:K)≠0) (pow_ne_zero 2 h343))
  have cfx := left_ne_zero_of_mul (fx ▸ mul_ne_zero (by norm_num : (-3292800:K)≠0) hX)
  have hc := mul_ne_zero (mul_ne_zero cf32 cf343) cfx
  have hp := left_ne_zero_of_mul (nj ▸ mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (6585600:K)≠0) h0) h32) h343)
  have hg : (c0 z)^2*normalizedKS (row z) R = (189000/(((row z).T-32)*((row z).T+343)*((row z).T-76832)))*(quotientJet z regTNum regTDen)^2 := by
    rw [hk,y_den]
    have hY : Y≠0 := hD
    have hj : quotientJet z regTNum regTDen=6585600*c0 z*c32 z*c343 z/Y^2 := (eq_div_iff (pow_ne_zero 2 hY)).mpr nj
    have h₁ := (eq_div_iff hY).mpr f32
    have h₂ := (eq_div_iff hY).mpr f343
    have h₃ := (eq_div_iff hY).mpr fx
    change (c0 z)^2*(-10080/((row z).X*Y))=_
    rw [h₁,h₂,h₃,hj]
    field_simp
    ring
  refine ⟨hp,hc,hg,?_⟩
  linear_combination (5/4)*hg
theorem from_original [CharZero K] (x : ℚ) (r₀ r₁ r₂ r₃ v : K) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₂ : r₂^2=42*(119136*(x:K)^2-76832)) (h₃ : r₃^2= -21*(119136*(x:K)^2+343)) (hv : v^2=5) :
    let z := zCoord r₀ r₁ r₃; let d := row z; let R := discRoot d v r₂
    Result d z R ∧ OriginalUniformMarkedMatrices318.Action v (qCoeff d r₀ R)
      (OriginalUniformSparseJet318.V0 d.m d.p d.q R) (OriginalUniformSparseJet318.V2 d.m d.p d.q R) := by
  let z := zCoord r₀ r₁ r₃
  have h := OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
  obtain ⟨_,h0,hy,_,hs⟩ := OriginalScalarEffectiveChart318.from_original r₀ r₁ r₃ x hx h₀ h₁ h₃
  have hf := OriginalScalarNamedUnits318.every_factor _ h0 hy hs
  have h32 := hf 9
  have h343 := hf 10
  change horner z [-1,-1,1]≠0 at h32
  change horner z [-1,4,1]≠0 at h343
  have H32 : c32 z≠0 := by convert h32 using 1; simp [c32,horner]; ring
  have H343 : c343 z≠0 := by convert h343 using 1; simp [c343,horner]; ring
  exact ⟨of_units z _ hy h.actual_laws.nzX h0 H32 H343 h.marked.evalKS, OriginalUniformMarkedMatrices318.on_sheet _ _ _ v hv h.marked⟩
end OriginalUniformOriginalTGauge318
#print axioms OriginalUniformOriginalTGauge318.from_original
