module
public import PELOriginalThetaSecondBounds318
public section
noncomputable section
namespace PELOriginalThetaDirectionalHolomorphy318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaHolomorphy318
open PELOriginalThetaSecondBounds318
variable (τ:ℂ)(hτ:0<τ.im)

/-- Actual continuous evaluation on the operator-norm derivative space,
so exchanging its value with the full convergent derivative series is justified. -/
@[expose] def evaluate(v:ComplexVectors):(ComplexVectors→L[ℂ]ℂ)→L[ℂ]ℂ:=
  (show (ComplexVectors→L[ℂ]ℂ)→ₗ[ℂ]ℂ from
    {toFun:=fun A=>A v
     map_add':=by intro A B;rfl
     map_smul':=by intro c A;rfl}).mkContinuous ‖v‖ (by
      intro A
      simpa only [mul_comm] using A.le_opNorm v)
lemma derivative_summable(z:ComplexVectors):Summable (fun n:Index=>derivative τ n z):=by
  let S:=max |(z 0).im| |(z 1).im|
  exact (derivativeBound_summable τ hτ S).of_norm_bounded
    (derivative_norm_bound τ hτ S z (le_max_left _ _) (le_max_right _ _))
lemma evaluate_term(v:ComplexVectors)(n:Index)(z:ComplexVectors):
    evaluate v (derivative τ n z)=directionalTerm τ v n z:=by
  simp only [evaluate,derivative,directionalTerm,coefficient,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring
lemma directional_summable(v z:ComplexVectors):
    Summable (fun n:Index=>directionalTerm τ v n z):=by
  have h:=(evaluate v).hasSum (derivative_summable τ hτ z).hasSum
  simpa only [evaluate_term] using h.summable
@[expose] def directionalTheta(v z:ComplexVectors):ℂ:=
  ∑'n:Index,directionalTerm τ v n z
lemma actual_derivative(v z:ComplexVectors):
    fderiv ℂ (theta τ) z v=directionalTheta τ v z:=by
  rw [(theta_hasFDerivAt τ hτ z).fderiv]
  have h:=(evaluate v).hasSum (derivative_summable τ hτ z).hasSum
  simp only [evaluate_term] at h
  exact h.tsum_eq.symm

/-- Full Frechet derivative of the directional theta function, obtained
from the actual locally uniform SECOND-derivative Gaussian bound. -/
lemma directional_hasFDerivAt(v z:ComplexVectors):
    HasFDerivAt (directionalTheta τ v)
      (∑'n:Index,secondDerivative τ v n z) z:=by
  let S:=‖z‖+1
  have hu:=secondBound_summable τ hτ S v
  have ho:IsOpen (Metric.ball z 1):=Metric.isOpen_ball
  have hp:IsPreconnected (Metric.ball z 1):=(convex_ball z 1).isPreconnected
  have hz:z∈Metric.ball z 1:=Metric.mem_ball_self (by norm_num)
  have hd:∀n:Index,∀w∈Metric.ball z 1,
      HasFDerivAt (directionalTerm τ v n) (secondDerivative τ v n w) w:=
    fun n w _=>PELOriginalThetaSecondBounds318.directional_hasFDerivAt τ v n w
  have hb:∀n:Index,∀w∈Metric.ball z 1,
      ‖secondDerivative τ v n w‖≤secondBound τ S v n:=by
    intro n w hw
    exact second_norm_bound τ hτ S v w (ball_im_bound z w hw 0) (ball_im_bound z w hw 1) n
  exact hasFDerivAt_tsum_of_isPreconnected hu ho hp hd hb hz
    (directional_summable τ hτ v z) hz

theorem directional_holomorphic(v:ComplexVectors):
    Differentiable ℂ (directionalTheta τ v):=
  fun z=>(directional_hasFDerivAt τ hτ v z).differentiableAt
end PELOriginalThetaDirectionalHolomorphy318
