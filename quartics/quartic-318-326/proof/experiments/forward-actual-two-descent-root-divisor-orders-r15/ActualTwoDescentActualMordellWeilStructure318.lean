module
public import ActualTwoDescentFreeFiniteDoublingIndex318
public section
noncomputable section
namespace ActualTwoDescentActualMordellWeilStructure318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentRationalHeightDescent318 ActualTwoDescentActualTwoTorsionCardinality318
open ActualTwoDescentDoublingIndexTransport318 ActualTwoDescentFreeFiniteDoublingIndex318

/-- An actual finitely generated rational elliptic group splits into a free
integer factor and a finite factor; its doubling index is exactly4*2^r. -/
theorem actual_mordell_weil_structure (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n)) :
    ∃ r : ℕ, ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (Point n ≃+ (Fin r →₀ ℤ) × T) ∧ Nat.card (DoubleQuotient n)=2^r*4 := by
  letI : AddGroup.FG (Point n) := actual_finite_generation n hn hf
  obtain ⟨r,ι,hι,p,hp,e,⟨equiv⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Point n)
  letI := hι
  letI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  have hT : Finite T := inferInstance
  refine ⟨r,T,inferInstance,hT,⟨equiv⟩,?_⟩
  rw [←actual_tagged_doubles_index]
  have h := actual_free_finite_index r T equiv
  rw [actual_doubling_kernel_card n hn] at h
  exact h

/-- The constructed quotient upper bound genuinely limits the free rank
in an ACTUAL Mordell-Weil decomposition to zero or one. -/
theorem actual_free_rank_at_most_one (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n))
    (hbound : Nat.card (DoubleQuotient n) ≤ 8) :
    ∃ r : ℕ, r ≤ 1 ∧ ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (Point n ≃+ (Fin r →₀ ℤ) × T) ∧ Nat.card (DoubleQuotient n)=2^r*4 := by
  obtain ⟨r,T,hT,hfin,he,hcard⟩ := actual_mordell_weil_structure n hn hf
  have hr : r ≤ 1 := by
    by_contra hr
    have hpow : 4 ≤ 2^r := by
      calc
        4=2^2 := by norm_num
        _≤2^r := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hcard] at hbound
    omega
  exact ⟨r,hr,T,hT,hfin,he,hcard⟩

end ActualTwoDescentActualMordellWeilStructure318
