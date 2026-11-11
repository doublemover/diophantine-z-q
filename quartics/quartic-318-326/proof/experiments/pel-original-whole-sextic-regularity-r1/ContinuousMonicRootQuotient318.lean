module
public import MonicRootProjectionOpen318
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Derivative
public section
noncomputable section
namespace ContinuousMonicRootQuotient318
open Polynomial
variable {E : Type*} [TopologicalSpace E]

@[expose] def quotient (p : E → Polynomial ℂ) (b : E → ℂ) (x : E) : Polynomial ℂ :=
  p x /ₘ (X-C (b x))

lemma factorization (p : E → Polynomial ℂ) (b : E → ℂ)
    (hb : ∀ x, (p x).IsRoot (b x)) (x : E) :
    (X-C (b x))*quotient p b x = p x :=
  Polynomial.mul_divByMonic_eq_iff_isRoot.mpr (hb x)

lemma monic (p : E → Polynomial ℂ) (b : E → ℂ)
    (hm : ∀ x, (p x).Monic) (hb : ∀ x, (p x).IsRoot (b x)) (x : E) :
    (quotient p b x).Monic :=
  (monic_X_sub_C (b x)).of_mul_monic_left ((factorization p b hb x).symm ▸ hm x)

lemma degree (p : E → Polynomial ℂ) (b : E → ℂ) (N : ℕ)
    (hd : ∀ x, (p x).natDegree = N) (x : E) :
    (quotient p b x).natDegree = N-1 := by
  rw [quotient,natDegree_divByMonic _ (monic_X_sub_C _),hd,natDegree_X_sub_C]

lemma coefficient_continuous (p : E → Polynomial ℂ) (b : E → ℂ) (N : ℕ)
    (hd : ∀ x, (p x).natDegree = N) (hp : ∀ k, Continuous (fun x => (p x).coeff k))
    (hb : Continuous b) (k : ℕ) : Continuous (fun x => (quotient p b x).coeff k) := by
  simp only [quotient,coeff_divByMonic_X_sub_C,hd]
  exact continuous_finset_sum _ (fun i _ => (hb.pow _).mul (hp i))

lemma evaluation_continuous (p : E → Polynomial ℂ) (b : E → ℂ) (N : ℕ)
    (hd : ∀ x, (p x).natDegree = N) (hp : ∀ k, Continuous (fun x => (p x).coeff k))
    (hb : Continuous b) (z : ℂ) : Continuous (fun x => (quotient p b x).eval z) := by
  simp only [Polynomial.eval_eq_sum_range,degree p b N hd]
  exact continuous_finset_sum _ (fun k _ =>
    (coefficient_continuous p b N hd hp hb k).mul continuous_const)

/-- Division removes exactly the specified continuous root branch.
The residual value there is the actual original polynomial derivative. -/
lemma value_eq_derivative (p : E → Polynomial ℂ) (b : E → ℂ)
    (hb : ∀ x, (p x).IsRoot (b x)) (x : E) :
    (quotient p b x).eval (b x) = (p x).derivative.eval (b x) := by
  have h := congrArg (fun q : Polynomial ℂ => q.derivative.eval (b x))
    (factorization p b hb x)
  simpa only [Polynomial.derivative_mul,Polynomial.derivative_sub,Polynomial.derivative_X,
    Polynomial.derivative_C,sub_zero,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_one,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    sub_self,one_mul,zero_mul,add_zero] using h

lemma root_of_quotient_root (p : E → Polynomial ℂ) (b : E → ℂ)
    (hb : ∀ x, (p x).IsRoot (b x)) (x : E) (z : ℂ)
    (hz : (quotient p b x).IsRoot z) : (p x).IsRoot z := by
  change (p x).eval z = 0
  rw [←factorization p b hb x,Polynomial.eval_mul,hz,mul_zero]
end ContinuousMonicRootQuotient318
