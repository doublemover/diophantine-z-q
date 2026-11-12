module
public import ComplexPolynomialOpenPoints318
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.Constructions
public section
noncomputable section
namespace LocalizedComplexCoefficientAnalytic318
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
abbrev Base := MvPolynomial ι ℂ

/-- Total extension used only to express ordinary ambient analyticity.
On the actual principal open it is the original localization evaluation. -/
@[expose] def value (d : Base) (a : Localization.Away d) (v : ι → ℂ) : ℂ :=
  if h : MvPolynomial.eval v d ≠ 0 then
    ComplexPolynomialOpenPoints318.evaluation d v h a else 0

@[simp] theorem value_on_open (d : Base) (a : Localization.Away d) (v : ι → ℂ)
    (hv : MvPolynomial.eval v d ≠ 0) :
    value d a v = ComplexPolynomialOpenPoints318.evaluation d v hv a := by
  simp only [value,dif_pos hv]

/-- Every element of the WHOLE localization, not just its polynomial
subring, has an exact rational expression on the same base open. -/
theorem exists_ratio (d : Base) (a : Localization.Away d) :
    ∃ b : Base, ∃ n : ℕ, ∀ (v : ι → ℂ), MvPolynomial.eval v d ≠ 0 →
      value d a v = MvPolynomial.eval v b / MvPolynomial.eval v d ^ n := by
  obtain ⟨⟨b,s⟩,he⟩ := IsLocalization.surj (Submonoid.powers d) a
  obtain ⟨n,hn⟩ := s.property
  refine ⟨b,n,?_⟩
  intro v hv
  have h := congrArg (ComplexPolynomialOpenPoints318.evaluation d v hv) he
  rw [map_mul,ComplexPolynomialOpenPoints318.evaluation_source,
    ComplexPolynomialOpenPoints318.evaluation_source,←hn,map_pow] at h
  rw [value_on_open d a v hv]
  exact (eq_div_iff (pow_ne_zero n hv)).mpr h

/-- Genuine complex analyticity of every original localized coefficient
at every point of its actual principal open. -/
theorem analyticAt_value (d : Base) (a : Localization.Away d) (v : ι → ℂ)
    (hv : MvPolynomial.eval v d ≠ 0) : AnalyticAt ℂ (value d a) v := by
  obtain ⟨b,n,he⟩ := exists_ratio d a
  have hb := (AnalyticOnNhd.eval_mvPolynomial b) v (Set.mem_univ v)
  have hd := (AnalyticOnNhd.eval_mvPolynomial d) v (Set.mem_univ v)
  apply (hb.div (hd.pow n) (pow_ne_zero n hv)).congr
  filter_upwards [hd.continuousAt.eventually_ne hv] with w hw
  exact (he w hw).symm
end LocalizedComplexCoefficientAnalytic318
