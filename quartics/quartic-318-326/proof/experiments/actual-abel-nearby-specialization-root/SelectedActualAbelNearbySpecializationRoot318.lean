module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.Order.OrderClosed

public section

open Filter Polynomial Topology
open scoped BigOperators Topology

namespace SelectedActualAbelNearbySpecializationRoot318

private theorem lower_bound_for_root_product (s : Multiset ℂ) (u : ℂ)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ a ∈ s, r ≤ ‖u - a‖) :
    r ^ s.card ≤ ‖(s.map (fun a => u - a)).prod‖ := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ih h
    have ha : r ≤ ‖u - a‖ := h a (by simp)
    have hs : ∀ b ∈ s, r ≤ ‖u - b‖ := fun b hb => h b (by simp [hb])
    simpa only [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons, norm_mul]
      using mul_le_mul ha (ih hs) (pow_nonneg hr _) (norm_nonneg (u - a))

/-- Small evaluation of the entire monic polynomial supplies a root
inside the given radius. The product estimate uses multiplicities, and
no enumeration continuous in the parameter is required. -/
theorem exists_root_of_norm_eval_lt
    (p : ℂ[X]) (hp : p.Monic) (u : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (he : ‖p.eval u‖ < r ^ p.natDegree) :
    ∃ a : ℂ, p.IsRoot a ∧ ‖u - a‖ < r := by
  by_contra h
  have hfar : ∀ a ∈ p.roots, r ≤ ‖u - a‖ := by
    intro a ha
    exact le_of_not_gt (fun hlt => h ⟨a, (Polynomial.mem_roots hp.ne_zero).1 ha, hlt⟩)
  have hs : p.Splits := IsAlgClosed.splits p
  have hb := lower_bound_for_root_product p.roots u r hr hfar
  rw [← hs.natDegree_eq_card_roots, ← hs.eval_eq_prod_roots_of_monic hp u] at hb
  exact (not_lt_of_ge hb) he

/-- Evaluating in the root variable and specializing the coefficient
parameter commute in the original complex polynomial ring. -/
theorem specialize_eval (p : ℂ[X][X]) (z u : ℂ) :
    (p.map (Polynomial.evalRingHom z)).eval u = (p.eval (Polynomial.C u)).eval z := by
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_C] using
    (Polynomial.eval_map_apply (p := p) (Polynomial.evalRingHom z) (Polynomial.C u))

private theorem complex_eval_continuous (p : ℂ[X]) : Continuous p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n c =>
    simpa only [Polynomial.eval_monomial] using
      (continuous_const : Continuous (fun _ : ℂ => c)).mul (continuous_id.pow n)

/-- Every prescribed root of the limiting monic specialization has
a nearby root of every sufficiently close specialization of the same
polynomial. No separability, exact root multiplicity, or chosen branch
is required. This is the analytic step used for the separating
multiplication characteristic polynomial at a bad fibre. -/
theorem eventually_specialized_root_near (p : ℂ[X][X]) (hp : p.Monic)
    (z₀ u : ℂ) (hroot : (p.map (Polynomial.evalRingHom z₀)).IsRoot u)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ z in 𝓝 z₀, ∃ a : ℂ, (p.map (Polynomial.evalRingHom z)).IsRoot a ∧ ‖u - a‖ < r := by
  let f : ℂ → ℂ := fun z => (p.map (Polynomial.evalRingHom z)).eval u
  have hf : Continuous f := by
    simpa only [f, specialize_eval] using complex_eval_continuous (p.eval (Polynomial.C u))
  have hopen : IsOpen {z : ℂ | ‖f z‖ < r ^ p.natDegree} :=
    isOpen_Iio.preimage hf.norm
  have hm : z₀ ∈ {z : ℂ | ‖f z‖ < r ^ p.natDegree} := by
    change ‖(p.map (Polynomial.evalRingHom z₀)).eval u‖ < r ^ p.natDegree
    have hzero : (p.map (Polynomial.evalRingHom z₀)).eval u = 0 := hroot
    rw [hzero, norm_zero]
    exact pow_pos hr _
  refine (hopen.eventually_mem hm).mono ?_
  intro z hz
  apply exists_root_of_norm_eval_lt (p.map (Polynomial.evalRingHom z))
    (hp.map (Polynomial.evalRingHom z)) u r hr.le
  rw [hp.natDegree_map (Polynomial.evalRingHom z)]
  exact hz

end SelectedActualAbelNearbySpecializationRoot318

#print axioms SelectedActualAbelNearbySpecializationRoot318.exists_root_of_norm_eval_lt
#print axioms SelectedActualAbelNearbySpecializationRoot318.eventually_specialized_root_near
