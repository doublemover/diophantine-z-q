module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace MonicComplexRootApproximation318
open Polynomial Filter
open scoped Topology

lemma norm_root_product_lower (s : Multiset ℂ) (z : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ r ∈ s, ε ≤ ‖z-r‖) :
    ε^s.card ≤ ‖(s.map (fun r => z-r)).prod‖ := by
  revert h
  induction s using Multiset.induction_on with
  | empty => intro h; simp
  | @cons r s ih =>
    intro h
    have hr := h r (Multiset.mem_cons_self _ _)
    have ht := ih (fun t ht => h t (Multiset.mem_cons_of_mem ht))
    simp only [Multiset.card_cons,Multiset.map_cons,Multiset.prod_cons,norm_mul,pow_succ]
    calc
      ε^s.card*ε ≤ ‖(s.map (fun t => z-t)).prod‖*‖z-r‖ :=
        mul_le_mul ht hr hε (norm_nonneg _)
      _ = _ := mul_comm _ _

/-- Small evaluation of a monic complex polynomial forces an actual
root nearby, even at multiple roots. The proof retains all root
multiplicities and needs no simple-root or chosen-branch hypothesis. -/
theorem exists_root_near (p : Polynomial ℂ) (hm : p.Monic) (z : ℂ)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ‖p.eval z‖ < ε^p.natDegree) :
    ∃ r : ℂ, p.IsRoot r ∧ ‖r-z‖ < ε := by
  by_contra! hn
  have hbound := norm_root_product_lower p.roots z ε hε.le (fun r hr => by
    have hroot := (Polynomial.mem_roots hm.ne_zero).mp hr
    simpa only [norm_sub_rev] using hn r hroot)
  have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm
    (Polynomial.card_roots_eq_natDegree (p := p))
  have he := congrArg (fun q : Polynomial ℂ => q.eval z) hp
  simp only [Polynomial.eval_multiset_prod,Multiset.map_map,Function.comp_def,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at he
  rw [Polynomial.card_roots_eq_natDegree,he] at hbound
  exact (not_lt_of_ge hbound) hsmall

/-- Every root of a continuous fixed-degree monic family is approached
by roots over EVERY sufficiently close base point, without separability.
Only evaluation continuity at the fixed original root is required. -/
theorem eventually_exists_root_near {E : Type*} [TopologicalSpace E]
    (p : E → Polynomial ℂ) (x : E) (z : ℂ) (N : ℕ)
    (hm : ∀ᶠ y in 𝓝 x, (p y).Monic)
    (hd : ∀ᶠ y in 𝓝 x, (p y).natDegree = N)
    (hc : ContinuousAt (fun y => (p y).eval z) x) (hz : (p x).eval z = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∃ r : ℂ, (p y).IsRoot r ∧ ‖r-z‖ < ε := by
  have hsmall : ∀ᶠ y in 𝓝 x, ‖(p y).eval z‖ < ε^N :=
    hc.norm.eventually (isOpen_Iio.mem_nhds (by simpa only [hz,norm_zero] using pow_pos hε N))
  filter_upwards [hm,hd,hsmall] with y hym hyd hys
  apply exists_root_near (p y) hym z ε hε
  simpa only [hyd] using hys
end MonicComplexRootApproximation318
