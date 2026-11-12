module
public import PELOriginalLiftDifferential318
public import ComplexPeriodicCoefficient318
public section
noncomputable section
namespace PELOriginalDifferentialConstant318
open Set Filter
open scoped Topology Manifold ContDiff
open PELOriginalInvolutionTower318 PELOriginalTorusCoverLift318
open OriginalInvolutionLegendreCharts318 PELOriginalIntegratedInvolutionCoordinates318
open PELOriginalLiftDifferential318 PELOriginalFourBranchCoordinate318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩

/-- True source periods preserve the derivative of the SAME lifted
original chart, by differentiating the actual global period identity. -/
lemma coordinate_derivative_periodic (a:Index i) (z t:ℂ)
    (ht:t∈PELOriginalInvolutionActualTorus318.periods i) (hz:z∈domain i a) :
    deriv (coordinate i a) (z+t)=deriv (coordinate i a) z := by
  have hperiod:∀w,universalLift i (w+t)=universalLift i w:=ht
  have hzt:z+t∈domain i a:=by
    change universalLift i (z+t)∈(actualChart i a).source
    rw [hperiod]
    exact hz
  have he:(fun w=>coordinate i a (w+t))=coordinate i a:=by
    funext w
    change actualChart i a (universalLift i (w+t))=actualChart i a (universalLift i w)
    rw [hperiod]
  have hd:HasDerivAt (fun w=>coordinate i a (w+t)) (deriv (coordinate i a) (z+t)) z:=by
    simpa only [mul_one] using (coordinate_analytic i a (z+t) hzt).differentiableAt.hasDerivAt.comp z
      ((hasDerivAt_id z).add_const t)
  rw [he] at hd
  exact hd.deriv.symm
lemma density_periodic (t:ℂ) (ht:t∈PELOriginalInvolutionActualTorus318.periods i) (z:ℂ) :
    density i (z+t)=density i z := by
  let a:=chosen i z
  have hz:z∈domain i a:=chosen_source i z
  have hperiod:∀w,universalLift i (w+t)=universalLift i w:=ht
  have hzt:z+t∈domain i a:=by
    change universalLift i (z+t)∈(actualChart i a).source
    rw [hperiod]
    exact hz
  rw [density_eq i a (z+t) hzt,density_eq i a z hz]
  unfold densityIn
  rw [coordinate_derivative_periodic i a z t ht hz]
  have hv:coordinate i a (z+t)=coordinate i a z:=congrArg (actualChart i a) (hperiod z)
  rw [hv]

/-- The local inverse is derived from the actual covering lift and the
original complex charts; differentiating its true inverse identity proves
nonzero derivative. No derivative hypothesis is added to uniformization. -/
lemma coordinate_derivative_ne (a:Index i) (z:ℂ) (hz:z∈domain i a):
    deriv (coordinate i a) z≠0 := by
  let h:=universalLift_localHomeomorph i
  let e:=h.localInverseAt z
  let K:OpenPartialHomeomorph ℂ ℂ:=e.symm.trans (actualChart i a)
  have hk:z∈K.source:=by
    refine ⟨h.self_mem_localInverseAt_target,?_⟩
    change e.symm z∈(actualChart i a).source
    rw [show (e.symm:ℂ→InvolutionBase i)=universalLift i from h.localInverseAt_symm z]
    exact hz
  have hK:(K:ℂ→ℂ)=coordinate i a:=by
    funext w
    change actualChart i a (e.symm w)=actualChart i a (universalLift i w)
    rw [show (e.symm:ℂ→InvolutionBase i)=universalLift i from h.localInverseAt_symm z]
  have hKa:AnalyticAt ℂ K z:=by rw [hK];exact coordinate_analytic i a z hz
  have hInv:=ComplexHolomorphicChartInverse318.inverse_analytic K hk hKa
  have hd:HasDerivAt (fun w=>K.symm (K w))
      (deriv K.symm (K z)*deriv K z) z:=
    hInv.differentiableAt.hasDerivAt.comp z hKa.differentiableAt.hasDerivAt
  have hid:HasDerivAt (fun w=>K.symm (K w)) 1 z:=by
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    filter_upwards [K.open_source.mem_nhds hk] with w hw
    exact K.left_inv hw
  have heq:=hd.unique hid
  rw [hK] at heq
  intro hzero
  rw [hzero,mul_zero] at heq
  exact zero_ne_one heq
lemma density_ne (z:ℂ):density i z≠0 := by
  rw [density_eq i (chosen i z) z (chosen_source i z)]
  exact mul_ne_zero
    (coefficient_ne i (PELOriginalIntegratedInvolutionCoordinates318.comparison i)
      (chosen i z) _ ((actualChart i (chosen i z)).map_source (chosen_source i z)))
    (coordinate_derivative_ne i (chosen i z) z (chosen_source i z))

/-- Compactness of the actual original source makes the ENTIRE original
pullback coefficient constant. The constant is genuinely nonzero because
both the original invariant form and actual covering derivative are. -/
@[expose] def scalar : ℂ:=density i 0
lemma scalar_ne : scalar i≠0:=density_ne i 0
lemma density_constant (z:ℂ):density i z=scalar i:=
  ComplexPeriodicCoefficient318.eq_at_zero (PELOriginalInvolutionActualTorus318.periods i)
    (density i) (density_analytic i) (density_periodic i) z
end PELOriginalDifferentialConstant318
