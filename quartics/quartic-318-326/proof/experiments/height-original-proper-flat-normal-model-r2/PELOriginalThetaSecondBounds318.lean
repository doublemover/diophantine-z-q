module
public import PELOriginalThetaHolomorphy318
public section
noncomputable section
namespace PELOriginalThetaSecondBounds318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalThetaHolomorphy318
open PELOriginalSiegelCoercivity318
variable (τ:ℂ)(hτ:0<τ.im)
@[expose] def coefficient(v:ComplexVectors)(n:Index):ℂ:=
  (2*(Real.pi:ℂ)*Complex.I)*linearMap n v
@[expose] def directionalTerm(v:ComplexVectors)(n:Index)(z:ComplexVectors):ℂ:=
  coefficient v n*term τ n z
@[expose] def secondDerivative(v:ComplexVectors)(n:Index)(z:ComplexVectors):
    ComplexVectors→L[ℂ]ℂ:=coefficient v n • derivative τ n z
lemma directional_hasFDerivAt(v:ComplexVectors)(n:Index)(z:ComplexVectors):
    HasFDerivAt (directionalTerm τ v n) (secondDerivative τ v n z) z:=
  (term_hasFDerivAt τ n z).const_mul (coefficient v n)
lemma coefficient_norm(v:ComplexVectors)(n:Index):
    ‖coefficient v n‖≤(2*Real.pi)*slope n*‖v‖:=by
  have hc:‖(2:ℂ)*(Real.pi:ℂ)*Complex.I‖=2*Real.pi:=by
    simp [norm_mul,Real.pi_pos.le]
  rw [coefficient,norm_mul,hc]
  calc
    _≤(2*Real.pi)*(‖linearMap n‖*‖v‖):=
      mul_le_mul_of_nonneg_left ((linearMap n).le_opNorm v) (by positivity)
    _≤(2*Real.pi)*(slope n*‖v‖):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (norm_linearMap n) (norm_nonneg v)) (by positivity)
    _=_:=by ring
@[expose] def weightedTwo(S:ℝ)(n:ℤ):ℝ:=|(n:ℝ)|^2*oneBound τ S n
@[expose] def secondBound(S:ℝ)(v:ComplexVectors)(n:Index):ℝ:=
  (8*Real.pi^2*‖v‖)*(weightedTwo τ S n.1*oneBound τ S n.2+
    oneBound τ S n.1*weightedTwo τ S n.2)
lemma weightedTwo_summable(S:ℝ):Summable (weightedTwo τ S):=by
  simpa only [weightedTwo,oneBound,Int.cast_abs] using
    summable_pow_mul_jacobiTheta₂_term_bound S (coercive_positive τ hτ) 2
lemma secondBound_summable(S:ℝ)(v:ComplexVectors):Summable (secondBound τ S v):=by
  have h0:=oneBound_summable τ hτ S
  have h2:=weightedTwo_summable τ hτ S
  have hn0:0≤oneBound τ S:=fun _=>(Real.exp_pos _).le
  have hn2:0≤weightedTwo τ S:=fun _=>mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  exact ((h2.mul_of_nonneg h0 hn2 hn0).add (h0.mul_of_nonneg h2 hn0 hn2)).mul_left _

/-- The second derivative bound is an actual quadratic-frequency
Gaussian on the WHOLE Z² series, not a pointwise formal derivative. -/
lemma second_norm_bound(S:ℝ)(v z:ComplexVectors)
    (h0:|(z 0).im|≤S)(h1:|(z 1).im|≤S)(n:Index):
    ‖secondDerivative τ v n z‖≤secondBound τ S v n:=by
  have hs:0≤slope n:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb:0≤bound τ S n:=mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hsq:(slope n)^2≤2*(|(n.1:ℝ)|^2+|(n.2:ℝ)|^2):=by
    dsimp [slope]
    nlinarith [sq_nonneg (|(n.1:ℝ)|-|(n.2:ℝ)|)]
  have hmul:=mul_le_mul_of_nonneg_left hsq
    (show 0≤4*Real.pi^2*‖v‖*bound τ S n by positivity)
  calc
    _=‖coefficient v n‖*‖derivative τ n z‖:=norm_smul _ _
    _≤((2*Real.pi)*slope n*‖v‖)*derivativeBound τ S n:=
      mul_le_mul (coefficient_norm v n) (derivative_norm_bound τ hτ S z h0 h1 n)
        (norm_nonneg _) (by positivity)
    _=(4*Real.pi^2*‖v‖*bound τ S n)*(slope n)^2:=by
      simp only [derivativeBound,weightedOne,bound,slope]
      ring
    _≤(4*Real.pi^2*‖v‖*bound τ S n)*
        (2*(|(n.1:ℝ)|^2+|(n.2:ℝ)|^2)):=hmul
    _=secondBound τ S v n:=by
      simp only [secondBound,weightedTwo,bound]
      ring
end PELOriginalThetaSecondBounds318
