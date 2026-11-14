module
public import PELOriginalThetaConvergence318
public section
noncomputable section
namespace PELOriginalThetaHolomorphy318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalSiegelCoercivity318
variable (τ:ℂ) (hτ:0<τ.im)
@[expose] def linearMap (n:Index):ComplexVectors→L[ℂ]ℂ:=
  (show ComplexVectors→ₗ[ℂ]ℂ from
    {toFun:=linear n
     map_add':=by intro z w;simp [linear];ring
     map_smul':=by intro a z;simp [linear];ring}).toContinuousLinearMap
@[expose] def slope (n:Index):ℝ:=|(n.1:ℝ)|+|(n.2:ℝ)|
lemma norm_linearMap (n:Index):‖linearMap n‖≤slope n:=by
  apply ContinuousLinearMap.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro z
  change ‖(n.1:ℂ)*z 0+(n.2:ℂ)*z 1‖≤slope n*‖z‖
  calc
    _≤‖(n.1:ℂ)*z 0‖+‖(n.2:ℂ)*z 1‖:=norm_add_le _ _
    _=|(n.1:ℝ)|*‖z 0‖+|(n.2:ℝ)|*‖z 1‖:=by simp [norm_mul]
    _≤|(n.1:ℝ)|*‖z‖+|(n.2:ℝ)|*‖z‖:=
      add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm z 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm z 1) (abs_nonneg _))
    _=slope n*‖z‖:=by simp only [slope];ring

@[expose] def derivative (n:Index) (z:ComplexVectors):ComplexVectors→L[ℂ]ℂ:=
  (term τ n z*(2*(Real.pi:ℂ)*Complex.I)) • linearMap n
lemma term_hasFDerivAt (n:Index) (z:ComplexVectors):
    HasFDerivAt (term τ n) (derivative τ n z) z:=by
  have h:=((linearMap n).hasFDerivAt (x:=z)).const_mul (2*(Real.pi:ℂ)*Complex.I)
  have he:=h.const_add ((Real.pi:ℂ)*Complex.I*quadratic τ n)
  have hexp:=(Complex.hasDerivAt_exp _).comp_hasFDerivAt z he
  convert hexp using 1
  ext v
  simp [derivative,term,linearMap,smul_smul]
  ring
@[expose] def weightedOne (S:ℝ) (n:ℤ):ℝ:=|(n:ℝ)|*oneBound τ S n
@[expose] def derivativeBound (S:ℝ) (n:Index):ℝ:=
  (2*Real.pi)*(weightedOne τ S n.1*oneBound τ S n.2+
    oneBound τ S n.1*weightedOne τ S n.2)
lemma weightedOne_summable (S:ℝ):Summable (weightedOne τ S):=by
  simpa only [weightedOne,oneBound,pow_one,Int.cast_abs] using
    summable_pow_mul_jacobiTheta₂_term_bound S (coercive_positive τ hτ) 1
lemma derivativeBound_summable (S:ℝ):Summable (derivativeBound τ S):=by
  have h0:=oneBound_summable τ hτ S
  have h1:=weightedOne_summable τ hτ S
  have hn0:0≤oneBound τ S:=fun _=>(Real.exp_pos _).le
  have hn1:0≤weightedOne τ S:=fun _=>mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  exact ((h1.mul_of_nonneg h0 hn1 hn0).add (h0.mul_of_nonneg h1 hn0 hn1)).mul_left _
lemma derivative_norm_bound (S:ℝ) (z:ComplexVectors)
    (h0:|(z 0).im|≤S) (h1:|(z 1).im|≤S) (n:Index):
    ‖derivative τ n z‖≤derivativeBound τ S n:=by
  have hconst:‖(2:ℂ)*(Real.pi:ℂ)*Complex.I‖=2*Real.pi:=by
    simp [norm_mul,Real.pi_pos.le]
  have hb:0≤bound τ S n:=mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hs:0≤slope n:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    _=‖term τ n z‖*(2*Real.pi)*‖linearMap n‖:=by
      simp only [derivative,norm_smul,norm_mul,hconst]
    _≤bound τ S n*(2*Real.pi)*slope n:=
      mul_le_mul (mul_le_mul_of_nonneg_right (norm_bound τ hτ S z h0 h1 n)
        (by positivity)) (norm_linearMap n) (norm_nonneg _) (mul_nonneg hb (by positivity))
    _=derivativeBound τ S n:=by
      simp only [derivativeBound,weightedOne,slope,bound]
      ring

lemma ball_im_bound (z w:ComplexVectors) (hw:w∈Metric.ball z 1) (j:Fin 2):
    |(w j).im|≤‖z‖+1:=by
  have hd:‖w-z‖<1:=by simpa only [Metric.mem_ball,dist_eq_norm] using hw
  have hn:‖w‖≤‖w-z‖+‖z‖:=by
    calc
      _=‖(w-z)+z‖:=by congr 1;abel
      _≤_:=norm_add_le _ _
  have hi:|(w j).im|≤‖w‖:=(Complex.abs_im_le_norm _).trans (norm_le_pi_norm w j)
  linarith
/-- Full complex Frechet derivative on C², obtained from locally uniform
summable derivative bounds. This is not merely separate-variable holomorphy. -/
theorem theta_hasFDerivAt (z:ComplexVectors):
    HasFDerivAt (theta τ) (∑'n:Index,derivative τ n z) z:=by
  let S:=‖z‖+1
  have hu:=derivativeBound_summable τ hτ S
  have ho:IsOpen (Metric.ball z 1):=Metric.isOpen_ball
  have hp:IsPreconnected (Metric.ball z 1):=(convex_ball z 1).isPreconnected
  have hz:z∈Metric.ball z 1:=Metric.mem_ball_self (by norm_num)
  have hd:∀n:Index,∀w∈Metric.ball z 1,
      HasFDerivAt (term τ n) (derivative τ n w) w:=fun n w _=>term_hasFDerivAt τ n w
  have hb:∀n:Index,∀w∈Metric.ball z 1,‖derivative τ n w‖≤derivativeBound τ S n:=by
    intro n w hw
    exact derivative_norm_bound τ hτ S w (ball_im_bound z w hw 0) (ball_im_bound z w hw 1) n
  exact hasFDerivAt_tsum_of_isPreconnected hu ho hp hd hb hz (summable τ hτ z) hz

theorem holomorphic:Differentiable ℂ (theta τ):=fun z=>(theta_hasFDerivAt τ hτ z).differentiableAt
end PELOriginalThetaHolomorphy318
