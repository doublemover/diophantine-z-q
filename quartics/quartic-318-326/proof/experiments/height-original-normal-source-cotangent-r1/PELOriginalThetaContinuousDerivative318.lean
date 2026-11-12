module
public import PELOriginalScaledThetaHolomorphy318
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public section
noncomputable section
namespace PELOriginalThetaContinuousDerivative318
open QuaternionicRealPeriod318 Filter Topology
open PELOriginalScaledThetaConvergence318 PELOriginalScaledThetaHolomorphy318
open PELOriginalThetaConvergence318 (Index)
open PELOriginalThetaHolomorphy318 (ball_im_bound)
variable (τ:ℂ) (hτ:0<τ.im) (a:ℝ) (ha:0<a)

lemma selectedDerivative_continuous (P:Index→Prop) [DecidablePred P] (n:Index):
    Continuous (selectedDerivative τ a P n):=by
  by_cases hn:P n
  · simp only [selectedDerivative,if_pos hn,derivative]
    exact ((continuous_iff_continuousAt.mpr (fun z=>(term_hasFDerivAt τ a n z).continuousAt)).mul
      continuous_const).smul continuous_const
  · simp only [selectedDerivative,if_neg hn]
    exact continuous_const

/-- The operator-valued derivative series is uniformly summable on each
actual ball. The residue predicate is fixed, not allowed to vary with z. -/
lemma derivative_sum_continuousAt (P:Index→Prop) [DecidablePred P]
    (z:ComplexVectors):
    ContinuousAt (fun w=>∑'n:Index,selectedDerivative τ a P n w) z:=by
  let S:ℝ:=‖z‖+1
  have hb:∀n:Index,∀w∈Metric.ball z 1,
      ‖selectedDerivative τ a P n w‖≤derivativeBound τ a S n:=by
    intro n w hw
    by_cases hn:P n
    · simpa only [selectedDerivative,if_pos hn] using
        derivative_norm_bound τ hτ a ha S w (ball_im_bound z w hw 0)
          (ball_im_bound z w hw 1) n
    · simp only [selectedDerivative,if_neg hn,norm_zero]
      unfold derivativeBound weightedOne oneBound
      positivity
  have hc:=continuousOn_tsum
    (fun n=>(selectedDerivative_continuous τ a P n).continuousOn)
    (derivativeBound_summable τ hτ a ha S) hb
  exact hc.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

lemma continuous_fderiv (P:Index→Prop) [DecidablePred P]:
    Continuous (fderiv ℂ (selectedTheta τ a P)):=by
  have he:fderiv ℂ (selectedTheta τ a P)=
      fun z=>∑'n:Index,selectedDerivative τ a P n z:=by
    funext z
    exact (selected_hasFDerivAt τ hτ a ha P z).fderiv
  rw [he]
  exact continuous_iff_continuousAt.mpr (derivative_sum_continuousAt τ hτ a ha P)

/-- Genuine C¹ regularity obtained from the convergent derivative series,
not a several-variable holomorphic-to-analytic shortcut. -/
theorem selected_contDiff_one (P:Index→Prop) [DecidablePred P]:
    ContDiff ℂ 1 (selectedTheta τ a P):=
  contDiff_one_iff_fderiv.mpr
    ⟨selected_holomorphic τ hτ a ha P,continuous_fderiv τ hτ a ha P⟩
end PELOriginalThetaContinuousDerivative318
