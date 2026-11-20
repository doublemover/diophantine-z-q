module
public import SelectedComplexOrdinaryBase318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.Connected.Basic
public section
noncomputable section
open Polynomial Set
open SelectedComplexOrdinaryBase318

namespace SelectedComplexConnectedNoSplit318

@[expose] def roots (p : Base[X]) : Set (Ordinary × ℂ) :=
  {z | p.eval₂ (evaluation z.1) z.2 = 0}

theorem roots_closed (p : Base[X]) : IsClosed (roots p) :=
  isClosed_eq (continuous_evaluation p) continuous_const

/-- Positive-degree monic factors have a complex root over a genuine
ordinary j; degree cannot drop in this specialization. -/
theorem root_exists (p : Base[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree) :
    (roots p).Nonempty := by
  let j : Ordinary := ⟨1,by norm_num⟩
  have hd : (p.map (evaluation j)).degree ≠ 0 := by
    rw [hp.degree_map _,degree_eq_natDegree hp.ne_zero]
    exact_mod_cast Nat.ne_of_gt hdeg
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_root (p.map (evaluation j)) hd
  refine ⟨(j,z),?_⟩
  change p.eval₂ (evaluation j) z = 0
  rw [eval₂_eq_eval_map]
  exact hz

theorem roots_mul (p q : Base[X]) : roots (p*q) = roots p ∪ roots q := by
  ext z
  change (p*q).eval₂ (evaluation z.1) z.2 = 0 ↔
    p.eval₂ (evaluation z.1) z.2 = 0 ∨ q.eval₂ (evaluation z.1) z.2 = 0
  rw [eval₂_mul,mul_eq_zero]

/-- A simple-root complex ordinary cover with connected whole root locus
cannot split into two positive-degree monic factors over the literal
complex coefficient base. This does not replace that root locus with
an arbitrarily chosen connected component. -/
theorem no_positive_monic_split (p a b : Base[X]) (ha : a.Monic) (hb : b.Monic)
    (haDeg : 0 < a.natDegree) (hbDeg : 0 < b.natDegree)
    (hc : IsPreconnected (roots p))
    (simple : ∀ z ∈ roots p, p.derivative.eval₂ (evaluation z.1) z.2 ≠ 0) :
    p ≠ a*b := by
  intro hprod
  have hcover : roots p = roots a ∪ roots b := by rw [hprod,roots_mul]
  have hdis : Disjoint (roots a) (roots b) := by
    apply Set.disjoint_left.mpr
    intro z hza hzb
    have hz : z ∈ roots p := by rw [hcover]; exact Or.inl hza
    apply simple z hz
    change a.eval₂ (evaluation z.1) z.2 = 0 at hza
    change b.eval₂ (evaluation z.1) z.2 = 0 at hzb
    simp only [hprod,derivative_mul,eval₂_add,eval₂_mul,hza,hzb,mul_zero,
      zero_mul,add_zero]
  have hu : roots p ⊆ (roots a)ᶜ ∪ (roots b)ᶜ := by
    intro z hz
    by_cases hza : z ∈ roots a
    · exact Or.inr (fun hzb => Set.disjoint_left.mp hdis hza hzb)
    · exact Or.inl hza
  obtain ⟨x,hx⟩ := root_exists a ha haDeg
  obtain ⟨y,hy⟩ := root_exists b hb hbDeg
  have hx' : x ∈ roots p ∩ (roots b)ᶜ :=
    ⟨by rw [hcover]; exact Or.inl hx,fun hxb => Set.disjoint_left.mp hdis hx hxb⟩
  have hy' : y ∈ roots p ∩ (roots a)ᶜ :=
    ⟨by rw [hcover]; exact Or.inr hy,fun hya => Set.disjoint_left.mp hdis hya hy⟩
  obtain ⟨z,hz,hza,hzb⟩ := hc _ _
    (roots_closed a).isOpen_compl (roots_closed b).isOpen_compl hu ⟨y,hy'⟩ ⟨x,hx'⟩
  rw [hcover] at hz
  exact hz.elim hza hzb

end SelectedComplexConnectedNoSplit318

#print axioms SelectedComplexConnectedNoSplit318.no_positive_monic_split
