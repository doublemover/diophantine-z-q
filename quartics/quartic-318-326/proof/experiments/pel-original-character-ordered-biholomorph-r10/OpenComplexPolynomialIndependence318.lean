module
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public section
noncomputable section
namespace OpenComplexPolynomialIndependence318
open Set Filter Topology
variable {ι:Type*}[Fintype ι]
/-- Genuine multivariable polynomial analyticity, followed by the
identity principle, proves uniqueness from ANY nonempty complex open.
No holomorphic-to-analytic shortcut for arbitrary maps is needed. -/
theorem eq_zero_of_open(p:MvPolynomial ι ℂ)(U:Set (ι→ℂ))
    (hU:IsOpen U)(hne:U.Nonempty)(hz:∀z∈U,MvPolynomial.eval z p=0):p=0:=by
  obtain ⟨x,hx⟩:=hne
  have he:(fun z=>MvPolynomial.eval z p)=ᶠ[𝓝 x] 0:=by
    filter_upwards [hU.mem_nhds hx] with z hzU
    exact hz z hzU
  have hall:=(AnalyticOnNhd.eval_mvPolynomial p).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ x) he
  apply MvPolynomial.funext
  intro z
  simpa only [map_zero] using hall (Set.mem_univ z)

/-- If genuine C-valued evaluations of specified algebra elements cover
an actual nonempty complex open, those elements are algebraically
independent in the ORIGINAL algebra. -/
theorem independent_of_open_evaluations {A:Type*}[CommRing A][Algebra ℂ A]
    (f:ι→A)(U:Set (ι→ℂ))(hU:IsOpen U)(hne:U.Nonempty)
    (he:∀w∈U,∃ev:A→ₐ[ℂ]ℂ,∀i,ev (f i)=w i):AlgebraicIndependent ℂ f:=by
  rw [algebraicIndependent_iff]
  intro p hp
  apply eq_zero_of_open p U hU hne
  intro w hw
  obtain ⟨ev,hev⟩:=he w hw
  have hmap:ev.comp (MvPolynomial.aeval f)=MvPolynomial.aeval w:=by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,MvPolynomial.aeval_X,hev]
  have h:=congrArg ev hp
  change (ev.comp (MvPolynomial.aeval f)) p=ev 0 at h
  rw [hmap,map_zero] at h
  exact h
end OpenComplexPolynomialIndependence318
