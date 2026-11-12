module
public import LocalizedComplexCoefficientAnalytic318
public import AnalyticParameterizedRootChart318
public import AdjoinRootSeparablePointCount318
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public section
noncomputable section
namespace LocalizedPrimitiveRootChart318
open Set Filter Polynomial
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable (d : MvPolynomial ι ℂ) (Q : Polynomial (Localization.Away d))

/-- Actual polynomial equation with the original localized coefficients;
outside the base open its total extension is irrelevant. -/
@[expose] def equation (p : (ι → ℂ) × ℂ) : ℂ :=
  ∑ n ∈ Q.support,
    LocalizedComplexCoefficientAnalytic318.value d (Q.coeff n) p.1 * p.2 ^ n

lemma equation_on_open (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) (z : ℂ) :
    equation d Q (v,z) =
      (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).eval z := by
  rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum,Polynomial.sum_def]
  simp only [equation,LocalizedComplexCoefficientAnalytic318.value_on_open d _ v hv]

lemma equation_analytic (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) (z : ℂ) :
    AnalyticAt ℂ (equation d Q) (v,z) := by
  unfold equation
  apply Finset.analyticAt_fun_sum
  intro n hn
  exact ((LocalizedComplexCoefficientAnalytic318.analyticAt_value d (Q.coeff n) v hv).comp
    analyticAt_fst).mul (analyticAt_snd.pow n)

lemma root_derivative (v : ι → ℂ) (hv : MvPolynomial.eval v d ≠ 0) (z : ℂ) :
    HasDerivAt (fun w => equation d Q (v,w))
      ((Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).derivative.eval z) z := by
  simpa only [equation_on_open d Q v hv] using
    (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).hasDerivAt z

/-- EVERY root of EVERY simple specialization on the actual base open
has its own genuine local analytic branch with full ambient uniqueness.
No assumption that it belongs to the original theta image is made. -/
theorem exists_root_graph (hs : Q.Separable) (v : ι → ℂ)
    (hv : MvPolynomial.eval v d ≠ 0) (z : ℂ)
    (hz : (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).eval z = 0) :
    ∃ g : (ι → ℂ) → ℂ, AnalyticAt ℂ g v ∧ g v = z ∧
      (∀ᶠ w in 𝓝 v, equation d Q (w,g w) = 0) ∧
      (∀ᶠ p in 𝓝 (v,z), equation d Q p = 0 ↔ g p.1 = p.2) := by
  have hd : (Q.map (ComplexPolynomialOpenPoints318.evaluation d v hv)).derivative.eval z ≠ 0 :=
    (hs.map).eval₂_derivative_ne_zero (RingHom.id ℂ) hz
  have he : equation d Q (v,z) = 0 := (equation_on_open d Q v hv z).trans hz
  simpa only [he] using AnalyticParameterizedRoot318.exists_graph
    (equation_analytic d Q v hv z) (root_derivative d Q v hv z) hd

/-- The chart is on the independently induced WHOLE root-locus topology,
not a topology transported from a chosen analytic sheet. Its coordinate
is exactly the original base vector, including both projected ratios. -/
theorem exists_root_chart (hs : Q.Separable)
    (p : AnalyticParameterizedRootChart318.ZeroLocus (equation d Q))
    (hp : MvPolynomial.eval p.val.1 d ≠ 0) :
    ∃ e : OpenPartialHomeomorph
        (AnalyticParameterizedRootChart318.ZeroLocus (equation d Q)) (ι → ℂ),
      p ∈ e.source ∧ (∀ q, e q = q.val.1) ∧
      AnalyticOnNhd ℂ (fun w => (e.symm w).val) e.target := by
  have hz : (Q.map (ComplexPolynomialOpenPoints318.evaluation d p.val.1 hp)).eval p.val.2 = 0 :=
    (equation_on_open d Q p.val.1 hp p.val.2).symm.trans p.property
  obtain ⟨g,hg,hg0,he,hu⟩ := exists_root_graph d Q hs p.val.1 hp p.val.2 hz
  exact AnalyticParameterizedRootChart318.exists_chart (equation d Q) p g hg hg0 he hu
end LocalizedPrimitiveRootChart318
