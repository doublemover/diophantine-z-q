module
public import ValuationNormChainExtraction
public section
namespace NormChainCompleteness
variable {K : Type*} [Field K]

/-- Exactly the residue dichotomy used by the final three detector chains:
negative valuation, or residue one. -/
@[expose] def Good (v : AddValuation K (WithTop ℤ)) (x : K) : Prop :=
  v x < 0 ∨ 0 < v (x-1)

theorem near_one_value (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : 0 < v (x-1)) : v x=0 := by
  simpa using v.map_eq_of_lt_sub (x:=1) (y:=x) (by simpa using h)

theorem near_one_square (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : 0 < v (x-1)) : 0 < v (x^2-1) := by
  have hx := near_one_value v x h
  have hp : 0 ≤ v (x+1) := by simpa [hx] using v.map_add x 1
  rw [show x^2-1=(x-1)*(x+1) by ring,v.map_mul]
  exact lt_of_lt_of_le h (le_add_of_nonneg_right hp)

theorem square_good (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : Good v x) : Good v (x^2) := by
  rcases h with h|h
  · left
    rw [v.map_pow]
    have hx : x ≠ 0 := by intro e; simp [e] at h
    obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx)
    rw [←ha]
    have hn : a<0 := by exact_mod_cast (ha ▸ h)
    exact_mod_cast (show 2*a<0 by omega)
  · exact Or.inr (near_one_square v x h)

theorem step_good (v : AddValuation K (WithTop ℤ)) (q x leaf : K)
    (hq : ValuationEvenNormChain.OddAt v q)
    (hl : ValuationEvenNormChain.EvenAt v leaf)
    (hx : Good v x) : Good v (x^2+q*leaf) := by
  rcases hl with hl|⟨b,hb,heb⟩
  · simpa [hl] using square_good v x hx
  obtain ⟨r,hr,hor⟩ := hq
  have ht : v (q*leaf)=((r+b:ℤ):WithTop ℤ) := by rw [v.map_mul,hr,hb]; norm_cast
  have hodd : Odd (r+b) := hor.add_even heb
  have hne : r+b ≠ 0 := by
    intro he
    simp [he] at hodd
  rcases hx with hx|hx
  · left
    have hx0 : x ≠ 0 := by intro e; simp [e] at hx
    obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx0)
    have hn : a<0 := by exact_mod_cast (ha ▸ hx)
    rw [ValuationEvenNormChain.step_value v q x leaf r a b hr ha.symm hb hor heb]
    exact_mod_cast (lt_of_le_of_lt (min_le_left (2*a) (r+b)) (show 2*a<0 by omega))
  · have hvx := near_one_value v x hx
    by_cases hn : r+b<0
    · left
      have heq := v.map_add_eq_of_lt_right (x:=x^2) (y:=q*leaf) (by
        rw [ht,v.map_pow,hvx]; simp only [nsmul_zero]; exact_mod_cast hn)
      rw [heq,ht]
      exact_mod_cast hn
    · right
      have hp : 0 < v (q*leaf) := by rw [ht]; exact_mod_cast (show 0<r+b by omega)
      have hsq := near_one_square v x hx
      have hh := lt_of_lt_of_le (lt_min hsq hp) (v.map_add (x^2-1) (q*leaf))
      simpa only [show x^2-1+q*leaf=x^2+q*leaf-1 by ring] using hh

theorem fold_good (v : AddValuation K (WithTop ℤ)) (leaves : List (K×K))
    (initial : K) (hi : Good v initial)
    (h : ∀ p∈leaves, ValuationEvenNormChain.OddAt v p.1 ∧
      ValuationEvenNormChain.EvenAt v p.2) :
    Good v (leaves.foldl (fun x p => x^2+p.1*p.2) initial) := by
  induction leaves generalizing initial with
  | nil => simpa using hi
  | cons p rest ih =>
    have hp := h p (by simp)
    have ht : ∀ p∈rest, ValuationEvenNormChain.OddAt v p.1 ∧
        ValuationEvenNormChain.EvenAt v p.2 := by
      intro x hx; exact h x (List.mem_cons_of_mem _ hx)
    exact ih _ (step_good v _ _ _ hp.1 hp.2 hi) ht

theorem actual_chain_good (v : AddValuation K (WithTop ℤ)) (leaves : List (K×K))
    (h : ∀ p∈leaves, ValuationEvenNormChain.OddAt v p.1 ∧
      ValuationEvenNormChain.EvenAt v p.2) :
    Good v (leaves.foldl (fun x p => x^2+p.1*p.2) 1) := by
  apply fold_good v leaves 1 _ h
  right
  simp

theorem good_nonzero (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : Good v x) : x ≠ 0 := by
  intro hx
  rcases h with h|h <;> simp [hx] at h

/-- At the unused split place, the reciprocal has residue zero or one. -/
theorem inverse_residue (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : Good v x) : 0 < v x⁻¹ ∨ 0 < v (x⁻¹-1) := by
  have hx := good_nonzero v x h
  rcases h with h|h
  · left
    obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx)
    have hn : a<0 := by exact_mod_cast (ha ▸ h)
    rw [v.map_inv,←ha]
    exact_mod_cast (show 0 < -a by omega)
  · right
    have hvx := near_one_value v x h
    rw [show x⁻¹-1=-(x-1)/x by field_simp; ring]
    rw [v.map_div,v.map_neg,hvx,sub_zero]
    exact h

theorem near_one_step (v : AddValuation K (WithTop ℤ)) (x t : K)
    (hx : 0 < v (x-1)) (ht : 0 < v t) :
    0 < v (x^2+t-1) := by
  have hh := lt_of_lt_of_le (lt_min (near_one_square v x hx) ht)
    (v.map_add (x^2-1) t)
  simpa only [show x^2-1+t=x^2+t-1 by ring] using hh

/-- At the selected place, the test depths make every weighted leaf small. -/
theorem fold_near_one (v : AddValuation K (WithTop ℤ)) (leaves : List (K×K))
    (initial : K) (hi : 0 < v (initial-1))
    (h : ∀ p∈leaves, 0 < v (p.1*p.2)) :
    0 < v ((leaves.foldl (fun x p => x^2+p.1*p.2) initial)-1) := by
  induction leaves generalizing initial with
  | nil => simpa using hi
  | cons p rest ih =>
    exact ih _ (near_one_step v _ _ hi (h p (by simp)))
      (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A successful reciprocal contributes one, the other contributes zero or
one, and odd residue characteristic prevents their trace from vanishing. -/
theorem trace_unit (v : AddValuation K (WithTop ℤ)) (a b : K)
    (h2 : v (2:K)=0) (ha : 0 < v (a-1))
    (hb : 0 < v b ∨ 0 < v (b-1)) : v (a+b)=0 := by
  rcases hb with hb|hb
  · apply near_one_value v (a+b)
    have hh := lt_of_lt_of_le (lt_min ha hb) (v.map_add (a-1) b)
    simpa only [show a-1+b=a+b-1 by ring] using hh
  · have hh := lt_of_lt_of_le (lt_min ha hb) (v.map_add (a-1) (b-1))
    have ht : 0 < v (a+b-2) := by
      simpa only [show a-1+(b-1)=a+b-2 by ring] using hh
    have heq := v.map_eq_of_lt_sub (x:=2) (y:=a+b) (by simpa [h2] using ht)
    simpa [h2] using heq

theorem near_one_inverse (v : AddValuation K (WithTop ℤ)) (x : K)
    (h : 0 < v (x-1)) : 0 < v (x⁻¹-1) := by
  rcases inverse_residue v x (Or.inr h) with hi|hi
  · have hx := near_one_value v x h
    simp [v.map_inv,hx] at hi
  · exact hi

/-- The final local completeness conclusion for the two split embeddings.
The right-hand leaf values can be negative or zero: parity, not squareness,
is the only requirement there. -/
theorem detector_trace_unit (v : AddValuation K (WithTop ℤ))
    (primary opposite : List (K×K)) (h2 : v (2:K)=0)
    (hp : ∀ p∈primary, 0 < v (p.1*p.2))
    (ho : ∀ p∈opposite, ValuationEvenNormChain.OddAt v p.1 ∧
      ValuationEvenNormChain.EvenAt v p.2) :
    v ((primary.foldl (fun x p => x^2+p.1*p.2) 1)⁻¹ +
      (opposite.foldl (fun x p => x^2+p.1*p.2) 1)⁻¹)=0 := by
  apply trace_unit v _ _ h2
  · apply near_one_inverse v
    exact fold_near_one v primary 1 (by simp) hp
  · exact inverse_residue v _ (actual_chain_good v opposite ho)

#print axioms detector_trace_unit
#print axioms actual_chain_good
#print axioms inverse_residue
#print axioms fold_near_one
#print axioms trace_unit
end NormChainCompleteness
