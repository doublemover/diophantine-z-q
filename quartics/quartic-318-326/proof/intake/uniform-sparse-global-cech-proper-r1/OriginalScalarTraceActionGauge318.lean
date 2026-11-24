module
public import OriginalMarkedScalarSeparableTrace318
public section
noncomputable section
namespace OriginalScalarTraceActionGauge318
open OriginalMarkedScalarSeparableTrace318 OriginalUniversalSparseTrace318
open OriginalUniformSparseJet318 OriginalUniformMarkedQMSurface318 OriginalUniformMarkedMatrices318
open OriginalUniformCentralTwistTransport318 OriginalUniformOriginalTGauge318 OriginalUniformCowanDerivative318
open OriginalUniformCowanData318
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
theorem moment_formula (d : Row K) (R u : K) (h : Laws d) (hh : Sheet d R u) (i : Fin 3) :
    moment (sexticData d R u h hh) i =
      factor (d.m+R) (d.m-R)/(2*R)*
        (![V0 d.m d.p d.q R,0,V2 d.m d.p d.q R] i) := by
  change -2*((rem _ _ _ _ i).coeff 5/(OriginalUniversalSparsePolynomial318.sextic (d.m+R) (d.m-R)).leadingCoeff)=_
  rw [entry _ _ _ _ hh.s_ne (denom_on d R u h hh)]
  fin_cases i <;> simp [diagS,diagT,V0,V2] <;> ring
/-- Quaternion action is adjoint for the true cohomological branch matrix, not
just for a proportional template. -/
theorem action_on_trace (d : Row K) (R u v : K) (hv : v^2=5) (h : Laws d) (hh : Sheet d R u) :
    let J:=sexticData d R u h hh
    moment J 1=0 ∧ Action v u (moment J 0) (moment J 2) := by
  dsimp only
  rw [moment_formula,moment_formula,moment_formula]
  let c:=factor (d.m+R) (d.m-R)/(2*R)
  change c*0=0 ∧ Action v u (c*V0 d.m d.p d.q R) (c*V2 d.m d.p d.q R)
  refine ⟨mul_zero c,split_action v u _ _ hv hh.u_ne ?_⟩
  linear_combination (factor (d.m+R) (d.m-R)/(2*R))*hh.self_adjoint

/-- The original scalar parameter, exact squared Hodge gauge, and faithful
quaternion pairing refer to the very same constructed marked separation data. -/
theorem from_original (x : ℚ) (r₀ r₁ r₂ r₃ v : K) (hx : x≠0)
    (h₀ : r₀^2= -14*(119136*(x:K)^2)) (h₁ : r₁^2= -6*(119136*(x:K)^2-32))
    (h₂ : r₂^2=42*(119136*(x:K)^2-76832)) (h₃ : r₃^2= -21*(119136*(x:K)^2+343))
    (hv : v^2=5) :
    let z:=zCoord r₀ r₁ r₃
    let d:=row z
    let R:=discRoot d v r₂
    let u:=qCoeff d r₀ R
    let h:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
    let J:=sexticData d R u h.actual_laws h.marked
    moment J 1=0 ∧ Action v u (moment J 0) (moment J 2) ∧
    (c0 z)^2*(rawI2 J.F/d.J*detMoment J)=
      (189000/((d.T-32)*(d.T+343)*(d.T-76832)))*(quotientJet z regTNum regTDen)^2 ∧
    (5/4)*(c0 z)^2*(rawI2 J.F/d.J*detMoment J)=
      (236250/((d.T-32)*(d.T+343)*(d.T-76832)))*(quotientJet z regTNum regTDen)^2 := by
  let z:=zCoord r₀ r₁ r₃
  let d:=row z
  let R:=discRoot d v r₂
  let u:=qCoeff d r₀ R
  have h:=OriginalUniformMarkedQMSurface318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv
  obtain ⟨off,act⟩:=action_on_trace d R u v hv h.actual_laws h.marked
  refine ⟨off,act,?_⟩
  have hg:=(OriginalUniformOriginalTGauge318.from_original x r₀ r₁ r₂ r₃ v hx h₀ h₁ h₂ h₃ hv).1
  have hn:=trace_on_sheet d R u h.actual_laws h.marked
  rw [←h.marked.evalKS] at hn
  exact ⟨hn.symm ▸ hg.algebraic,hn.symm ▸ hg.theta_scaled⟩
end OriginalScalarTraceActionGauge318
#print axioms OriginalScalarTraceActionGauge318.from_original
