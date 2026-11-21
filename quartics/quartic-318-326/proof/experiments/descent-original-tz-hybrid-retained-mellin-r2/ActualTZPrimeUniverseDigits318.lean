module
public import Mathlib
public section
noncomputable section
namespace ActualTZPrimeUniverseDigits318
open scoped BigOperators ArithmeticFunction.Moebius

abbrev Subsets (P : ℕ) := {s : Finset ℕ // s ⊆ Nat.primesBelow P}
abbrev Supported (P : ℕ) :=
  {d : ℕ // Squarefree d ∧ d.primeFactors ⊆ Nat.primesBelow P}

theorem product_squarefree (s : Finset ℕ) (hp : ∀ p∈s,p.Prime) :
    Squarefree (∏ p∈s,p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hs ih =>
    have hP := hp p (Finset.mem_insert_self _ _)
    have hS (q : ℕ) (hq : q∈s) := hp q (Finset.mem_insert_of_mem hq)
    have hC : (∏ q∈s,q).Coprime p := by
      apply Nat.Coprime.prod_left
      intro q hq
      exact (Nat.coprime_primes (hS q hq) hP).2 (fun h => hs (h ▸ hq))
    rw [Finset.prod_insert hs,Nat.squarefree_mul_iff]
    exact ⟨hC.symm,hP.squarefree,ih hS⟩

/-- The one-slot inverse between finite prime support and literal
squarefree positive digits. Apply independently to both slots of each
original row; the size cutoff is not baked into this equivalence. -/
def equiv (P : ℕ) : Subsets P ≃ Supported P where
  toFun s := ⟨∏ p∈s.val,p,
    product_squarefree s.val (fun _ hp => Nat.prime_of_mem_primesBelow (s.property hp)),
    by
      rw [Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primesBelow (s.property hp))]
      exact s.property⟩
  invFun d := ⟨d.val.primeFactors,d.property.2⟩
  left_inv s := by
    apply Subtype.ext
    exact Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primesBelow (s.property hp))
  right_inv d := by
    apply Subtype.ext
    exact Nat.prod_primeFactors_of_squarefree d.property.1

theorem equiv_apply_val (P : ℕ) (s : Subsets P) :
    (equiv P s).val=∏ p∈s.val,p := by unfold equiv; rfl

/-- Every original squarefree divisor d≤floor R is represented if
P>floor R. A supported digit that happens to exceed that exact cutoff
is still represented and is discarded later by the actual cutoff. -/
theorem represented (P d : ℕ) (hd : Squarefree d) (hP : d<P) :
    ∃ s : Subsets P,(equiv P s).val=d := by
  have hs : d.primeFactors ⊆ Nat.primesBelow P := by
    intro p hp
    obtain ⟨hprime,hdiv,hne⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesBelow.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv).trans_lt hP,hprime⟩
  let u : Supported P := ⟨d,hd,hs⟩
  refine ⟨(equiv P).symm u,?_⟩
  exact congrArg Subtype.val ((equiv P).apply_symm_apply u)

theorem signed_mobius (s : Finset ℕ) (hp : ∀ p∈s,p.Prime) :
    μ (∏ p∈s,p) = ∏ _p∈s,(-1:ℤ) := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (product_squarefree s hp),
    Nat.primeFactors_prod hp,Finset.prod_const]

private theorem positive_mul_cpow (v w : ℝ) (hv : 0<v) (hw : 0<w) (z : ℂ) :
    ((v*w:ℝ):ℂ)^z=(v:ℂ)^z*(w:ℂ)^z := by
  have hV := Complex.ofReal_ne_zero.mpr hv.ne'
  have hW := Complex.ofReal_ne_zero.mpr hw.ne'
  have hVW := Complex.ofReal_ne_zero.mpr (mul_pos hv hw).ne'
  rw [Complex.cpow_def_of_ne_zero hVW,Complex.cpow_def_of_ne_zero hV,Complex.cpow_def_of_ne_zero hW,
    ←Complex.exp_add,←Complex.ofReal_log (mul_nonneg hv.le hw.le),
    ←Complex.ofReal_log hv.le,←Complex.ofReal_log hw.le,
    Real.log_mul hv.ne' hw.ne',Complex.ofReal_add,add_mul]

theorem cpow_product (s : Finset ℕ) (h : ∀ p∈s,0<p) (z : ℂ) :
    ((∏ p∈s,p : ℕ):ℂ)^z=∏ p∈s,(p:ℂ)^z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hs ih =>
      have hp : (0:ℝ)<p := by exact_mod_cast h p (Finset.mem_insert_self _ _)
      have hS (q : ℕ) (hq : q∈s) := h q (Finset.mem_insert_of_mem hq)
      have H : (0:ℝ)<((∏ q∈s,q : ℕ):ℝ) := by
        exact_mod_cast Finset.prod_pos hS
      rw [Finset.prod_insert hs,Finset.prod_insert hs,←Complex.ofReal_natCast,Nat.cast_mul,
        positive_mul_cpow _ _ hp H,Complex.ofReal_natCast,Complex.ofReal_natCast,ih hS]

end ActualTZPrimeUniverseDigits318
