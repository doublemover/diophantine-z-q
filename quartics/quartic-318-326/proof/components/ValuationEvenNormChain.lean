module
public import ValuationCurveParity
public section
namespace ValuationEvenNormChain
variable {K : Type*} [Field K]

@[expose] def EvenAt (v : AddValuation K (WithTop ℤ)) (x : K) : Prop :=
  x=0 ∨ ∃ n : ℤ, v x=n ∧ Even n
@[expose] def OddAt (v : AddValuation K (WithTop ℤ)) (x : K) : Prop :=
  ∃ n : ℤ, v x=n ∧ Odd n

theorem square_even (v : AddValuation K (WithTop ℤ)) (x : K) : EvenAt v (x^2) := by
  by_cases hx : x=0
  · exact Or.inl (by simp [hx])
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hx)
  refine Or.inr ⟨2*a,?_,⟨a,by omega⟩⟩
  rw [v.map_pow,←ha]
  norm_cast

theorem delta_even (v : AddValuation K (WithTop ℤ)) (D u y : K)
    (hD : v D=0) (h2 : v (2:K)=0) (hc : y^2=1-D*u^4) : EvenAt v (y-1) := by
  by_cases hd : y-1=0
  · exact Or.inl hd
  · exact Or.inr (ValuationCurveParity.delta_even v D u y hD h2 hc hd)

theorem step_value (v : AddValuation K (WithTop ℤ)) (q previous leaf : K)
    (r a b : ℤ) (hr : v q=r) (ha : v previous=a) (hb : v leaf=b)
    (hor : Odd r) (heb : Even b) :
    v (previous^2+q*leaf) = ((min (2*a) (r+b) : ℤ) : WithTop ℤ) := by
  have hne : v (previous^2) ≠ v (q*leaf) := by
    rw [v.map_pow,v.map_mul,ha,hr,hb]
    intro heq
    have hi : 2*a=r+b := by exact_mod_cast heq
    obtain ⟨i,hi⟩ := heb
    obtain ⟨j,hj⟩ := hor
    omega
  rw [v.map_add_of_distinct_val hne,v.map_pow,v.map_mul,ha,hr,hb]
  norm_cast

/-- At an odd-weight place, any even-valuation leaf is allowed. No global
square root of the leaf is asserted or needed. -/
theorem step_nonzero (v : AddValuation K (WithTop ℤ)) (q previous leaf : K)
    (hq : OddAt v q) (hleaf : EvenAt v leaf) (hp : previous ≠ 0) :
    previous^2+q*leaf ≠ 0 := by
  rcases hleaf with hz | ⟨b,hb,heb⟩
  · simpa [hz] using pow_ne_zero 2 hp
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hp)
  obtain ⟨r,hr,hor⟩ := hq
  have hne : v (previous^2) ≠ v (q*leaf) := by
    rw [v.map_pow,v.map_mul,←ha,hr,hb]
    intro heq
    have hi : 2*a=r+b := by exact_mod_cast heq
    obtain ⟨i,hi⟩ := heb
    obtain ⟨j,hj⟩ := hor
    omega
  intro hz
  have hm := v.map_add_of_distinct_val hne
  rw [hz,v.map_zero] at hm
  have hpfin : v (previous^2)<⊤ :=
    lt_top_iff_ne_top.mpr ((v.ne_top_iff).mpr (pow_ne_zero 2 hp))
  have hh := lt_of_le_of_lt (min_le_left (v (previous^2)) (v (q*leaf))) hpfin
  rw [←hm] at hh
  exact (lt_irrefl _ hh)

theorem fold_nonzero (v : AddValuation K (WithTop ℤ))
    (leaves : List (K×K)) (initial : K)
    (h : ∀ p ∈ leaves, OddAt v p.1 ∧ EvenAt v p.2) (hi : initial ≠ 0) :
    leaves.foldl (fun previous p => previous^2+p.1*p.2) initial ≠ 0 := by
  induction leaves generalizing initial with
  | nil => simpa using hi
  | cons p rest ih =>
    have hp := h p (by simp)
    have ht : ∀ x ∈ rest, OddAt v x.1 ∧ EvenAt v x.2 := by
      intro x hx
      exact h x (List.mem_cons_of_mem _ hx)
    simpa only [List.foldl_cons] using
      ih (initial^2+p.1*p.2) ht (step_nonzero v p.1 initial p.2 hp.1 hp.2 hi)

/-- A zero chain rules out every place satisfying the consumed-contact
odd-weight/even-leaf conditions. -/
theorem zero_excludes_contact (v : AddValuation K (WithTop ℤ))
    (leaves : List (K×K))
    (hz : leaves.foldl (fun previous p => previous^2+p.1*p.2) 1=0) :
    ¬ (∀ p ∈ leaves, OddAt v p.1 ∧ EvenAt v p.2) := by
  intro h
  exact fold_nonzero v leaves 1 h one_ne_zero hz
end ValuationEvenNormChain
