module
public import PELOriginalScaledThetaConvergence318
public import PELOriginalThetaHolomorphy318
public section
noncomputable section
namespace PELOriginalScaledThetaHolomorphy318
open QuaternionicRealPeriod318 PELOriginalScaledThetaConvergence318 PELOriginalSiegelCoercivity318
open PELOriginalThetaConvergence318 (Index quadratic linear)
open PELOriginalThetaHolomorphy318 (linearMap slope norm_linearMap ball_im_bound)
variable (τ:ℂ) (hτ:0<τ.im)
variable (a:ℝ) (ha:0<a)
@[expose] def derivative (n:Index) (z:ComplexVectors):ComplexVectors→L[ℂ]ℂ:=
  (term τ a n z*(2*(Real.pi:ℂ)*Complex.I)) • linearMap n
lemma term_hasFDerivAt (n:Index) (z:ComplexVectors):
    HasFDerivAt (term τ a n) (derivative τ a n z) z:=by
  have h:=((linearMap n).hasFDerivAt (x:=z)).const_mul (2*(Real.pi:ℂ)*Complex.I)
  have he:=h.const_add ((Real.pi:ℂ)*Complex.I*(a:ℂ)*quadratic τ n)
  have hexp:=(Complex.hasDerivAt_exp _).comp_hasFDerivAt z he
  convert hexp using 1
  ext v
  simp [derivative,term,linearMap,smul_smul]
  ring
@[expose] def weightedOne (S:ℝ) (n:ℤ):ℝ:=|(n:ℝ)|*oneBound τ a S n
@[expose] def derivativeBound (S:ℝ) (n:Index):ℝ:=
  (2*Real.pi)*(weightedOne τ a S n.1*oneBound τ a S n.2+
    oneBound τ a S n.1*weightedOne τ a S n.2)
lemma weightedOne_summable (S:ℝ):Summable (weightedOne τ a S):=by
  simpa only [weightedOne,oneBound,pow_one,Int.cast_abs] using
    summable_pow_mul_jacobiTheta₂_term_bound S (mul_pos ha (coercive_positive τ hτ)) 1
lemma derivativeBound_summable (S:ℝ):Summable (derivativeBound τ a S):=by
  have h0:=oneBound_summable τ hτ a ha S
  have h1:=weightedOne_summable τ hτ a ha S
  have hn0:0≤oneBound τ a S:=fun _=>(Real.exp_pos _).le
  have hn1:0≤weightedOne τ a S:=fun _=>mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  exact ((h1.mul_of_nonneg h0 hn1 hn0).add (h0.mul_of_nonneg h1 hn0 hn1)).mul_left _
lemma derivative_norm_bound (S:ℝ) (z:ComplexVectors)
    (h0:|(z 0).im|≤S) (h1:|(z 1).im|≤S) (n:Index):
    ‖derivative τ a n z‖≤derivativeBound τ a S n:=by
  have hconst:‖(2:ℂ)*(Real.pi:ℂ)*Complex.I‖=2*Real.pi:=by
    simp [norm_mul,Real.pi_pos.le]
  have hb:0≤bound τ a S n:=mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hs:0≤slope n:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    _=‖term τ a n z‖*(2*Real.pi)*‖linearMap n‖:=by
      simp only [derivative,norm_smul,norm_mul,hconst]
    _≤bound τ a S n*(2*Real.pi)*slope n:=
      mul_le_mul (mul_le_mul_of_nonneg_right (norm_bound τ hτ a ha S z h0 h1 n)
        (by positivity)) (norm_linearMap n) (norm_nonneg _) (mul_nonneg hb (by positivity))
    _=derivativeBound τ a S n:=by
      simp only [derivativeBound,weightedOne,slope,bound]
      ring

/-- A fixed frequency subset, selected BEFORE evaluation in C². -/
@[expose] def selectedTerm (P:Index→Prop) [DecidablePred P] (n:Index)
    (z:ComplexVectors):ℂ:=if P n then term τ a n z else 0
@[expose] def selectedDerivative (P:Index→Prop) [DecidablePred P] (n:Index)
    (z:ComplexVectors):ComplexVectors→L[ℂ]ℂ:=if P n then derivative τ a n z else 0
lemma selected_summable (P:Index→Prop) [DecidablePred P] (z:ComplexVectors):
    Summable (fun n=>selectedTerm τ a P n z):=by
  let S:=max |(z 0).im| |(z 1).im|
  apply (bound_summable τ hτ a ha S).of_norm_bounded
  intro n
  by_cases hn:P n
  · simpa only [selectedTerm,if_pos hn] using
      norm_bound τ hτ a ha S z (le_max_left _ _) (le_max_right _ _) n
  · simp only [selectedTerm,if_neg hn,norm_zero]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
@[expose] def selectedTheta (P:Index→Prop) [DecidablePred P]
    (z:ComplexVectors):ℂ:=∑'n:Index,selectedTerm τ a P n z
lemma selected_hasFDerivAt (P:Index→Prop) [DecidablePred P] (z:ComplexVectors):
    HasFDerivAt (selectedTheta τ a P) (∑'n:Index,selectedDerivative τ a P n z) z:=by
  let S:=‖z‖+1
  have hu:=derivativeBound_summable τ hτ a ha S
  have ho:IsOpen (Metric.ball z 1):=Metric.isOpen_ball
  have hp:IsPreconnected (Metric.ball z 1):=(convex_ball z 1).isPreconnected
  have hz:z∈Metric.ball z 1:=Metric.mem_ball_self (by norm_num)
  have hd:∀n:Index,∀w∈Metric.ball z 1,
      HasFDerivAt (selectedTerm τ a P n) (selectedDerivative τ a P n w) w:=by
    intro n w hw
    by_cases hn:P n
    · simpa only [selectedTerm,selectedDerivative,if_pos hn] using term_hasFDerivAt τ a n w
    · simpa only [selectedTerm,selectedDerivative,if_neg hn] using
        (hasFDerivAt_const w (0:ℂ))
  have hb:∀n:Index,∀w∈Metric.ball z 1,
      ‖selectedDerivative τ a P n w‖≤derivativeBound τ a S n:=by
    intro n w hw
    by_cases hn:P n
    · simpa only [selectedDerivative,if_pos hn] using
        derivative_norm_bound τ hτ a ha S w (ball_im_bound z w hw 0) (ball_im_bound z w hw 1) n
    · simp only [selectedDerivative,if_neg hn,norm_zero]
      unfold derivativeBound weightedOne oneBound
      positivity
  exact hasFDerivAt_tsum_of_isPreconnected hu ho hp hd hb hz
    (selected_summable τ hτ a ha P z) hz

/-- Full complex holomorphy of EVERY actual characteristic subseries,
from summable local derivative bounds, not separate-variable reasoning. -/
theorem selected_holomorphic (P:Index→Prop) [DecidablePred P]:
    Differentiable ℂ (selectedTheta τ a P):=
  fun z=>(selected_hasFDerivAt τ hτ a ha P z).differentiableAt
end PELOriginalScaledThetaHolomorphy318
