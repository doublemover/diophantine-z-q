module
public import PELOriginalThetaConvergence318
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public section
noncomputable section
namespace PELOriginalScaledThetaConvergence318
open QuaternionicRealPeriod318 PELOriginalSiegelMatrix318 PELOriginalSiegelCoercivity318
variable (τ:ℂ) (hτ:0<τ.im)
open PELOriginalThetaConvergence318 (Index quadratic linear)
variable (a:ℝ) (ha:0<a)
@[expose] def term (n:Index) (z:ComplexVectors):ℂ:=
  Complex.exp ((Real.pi:ℂ)*Complex.I*(a:ℂ)*quadratic τ n+2*(Real.pi:ℂ)*Complex.I*linear n z)
@[expose] def oneBound (S:ℝ) (n:ℤ):ℝ:=
  Real.exp (-Real.pi*((a*coercive τ)*(n:ℝ)^2-2*S*|(n:ℝ)|))
@[expose] def bound (S:ℝ) (n:Index):ℝ:=oneBound τ a S n.1*oneBound τ a S n.2
lemma norm_term (n:Index) (z:ComplexVectors):
    ‖term τ a n z‖=Real.exp (-Real.pi*(a*energy τ ![(n.1:ℝ),(n.2:ℝ)]+
      2*((n.1:ℝ)*(z 0).im+(n.2:ℝ)*(z 1).im))):=by
  simp [term,Complex.ofReal_mul,Complex.norm_exp,quadratic,linear,energy,imaginary,Complex.mul_re,Complex.mul_im]
  congr 1 <;> ring
lemma oneBound_summable (S:ℝ):Summable (oneBound τ a S):=by
  simpa only [oneBound,pow_zero,one_mul,Int.cast_abs] using
    summable_pow_mul_jacobiTheta₂_term_bound S (mul_pos ha (coercive_positive τ hτ)) 0
lemma bound_summable (S:ℝ):Summable (bound τ a S):=
  (oneBound_summable τ hτ a ha S).mul_of_nonneg (oneBound_summable τ hτ a ha S)
    (fun _=>(Real.exp_pos _).le) (fun _=>(Real.exp_pos _).le)
lemma norm_bound (S:ℝ) (z:ComplexVectors)
    (hz0:|(z 0).im|≤S) (hz1:|(z 1).im|≤S) (n:Index):
    ‖term τ a n z‖≤bound τ a S n:=by
  have h0: -|(n.1:ℝ)|*S≤(n.1:ℝ)*(z 0).im:=by
    have h:=mul_le_mul_of_nonneg_left hz0 (abs_nonneg (n.1:ℝ))
    rw [←abs_mul] at h
    linarith [neg_abs_le ((n.1:ℝ)*(z 0).im)]
  have h1: -|(n.2:ℝ)|*S≤(n.2:ℝ)*(z 1).im:=by
    have h:=mul_le_mul_of_nonneg_left hz1 (abs_nonneg (n.2:ℝ))
    rw [←abs_mul] at h
    linarith [neg_abs_le ((n.2:ℝ)*(z 1).im)]
  have he:=energy_lower τ hτ ![(n.1:ℝ),(n.2:ℝ)]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at he
  have hsum:(a*coercive τ)*((n.1:ℝ)^2+(n.2:ℝ)^2)-
      2*S*(|(n.1:ℝ)|+|(n.2:ℝ)|)≤
      a*energy τ ![(n.1:ℝ),(n.2:ℝ)]+2*((n.1:ℝ)*(z 0).im+(n.2:ℝ)*(z 1).im):=by
    have hea:=mul_le_mul_of_nonneg_left he ha.le
    nlinarith
  rw [norm_term]
  simp only [bound,oneBound,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp:=mul_le_mul_of_nonneg_left hsum Real.pi_pos.le
  nlinarith

/-- Genuine absolute convergence for EVERY positive real quadratic scaling
of the SAME original quaternionic period matrix. The linear frequency is
unchanged, permitting characteristic subseries for actual power lines. -/
lemma summable (z:ComplexVectors):Summable (fun n:Index=>term τ a n z):=by
  let S:=max |(z 0).im| |(z 1).im|
  exact (bound_summable τ hτ a ha S).of_norm_bounded
    (norm_bound τ hτ a ha S z (le_max_left _ _) (le_max_right _ _))
@[expose] def theta (z:ComplexVectors):ℂ:=∑'n:Index,term τ a n z
lemma hasSum (z:ComplexVectors):HasSum (fun n:Index=>term τ a n z) (theta τ a z):=
  (summable τ hτ a ha z).hasSum
end PELOriginalScaledThetaConvergence318
