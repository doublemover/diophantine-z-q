module
public import Mathlib
public section
noncomputable section
namespace ActualTZResidueIntervalCount318
open scoped BigOperators

def natHits (q L r : ℕ) : ℕ := ∑ t∈Finset.range L,if t%q=r then 1 else 0

@[expose] def intHits (q L : ℕ) (s r : ℤ) : ℕ :=
  ∑ t∈Finset.range L,if Int.ModEq (q:ℤ) (s+(t:ℤ)) r then 1 else 0

private theorem short_span (q L r : ℕ) (hL : L≤q) :
    natHits q L r=if r<L then 1 else 0 := by
  classical
  unfold natHits
  calc
    _ = ∑ t∈Finset.range L, if t=r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.mod_eq_of_lt ((Finset.mem_range.mp ht).trans_le hL)]
    _ = _ := by simp only [Finset.sum_ite_eq',Finset.mem_range]

private theorem period (q L k r : ℕ) :
    natHits q (q*k+L) r=natHits q (q*k) r+natHits q L r := by
  unfold natHits
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [Nat.add_comm (q*k) t,Nat.add_mul_mod_self_left]

private theorem blocks (q r : ℕ) (hr : r<q) (k : ℕ) :
    natHits q (q*k) r=k := by
  induction k with
  | zero => simp [natHits]
  | succ k ih =>
      rw [Nat.mul_succ,period,ih,short_span _ _ _ le_rfl,if_pos hr]

theorem exact_nat_count (q L r : ℕ) (hq : 0<q) (hr : r<q) :
    natHits q L r = L/q+(if r<L%q then 1 else 0) := by
  calc
    _ = natHits q (q*(L/q)+L%q) r := congrArg (fun n => natHits q n r) (Nat.div_add_mod L q).symm
    _ = _ := by rw [period,blocks q r hr,short_span _ _ _ (Nat.mod_lt L hq).le]

/-- Every integer offset, including a negative start, reduces to the
one true canonical residue r-s modulo q. -/
theorem int_eq_nat (q L : ℕ) (s r : ℤ) (hq : 0<q) :
    intHits q L s r = natHits q L ((r-s)%(q:ℤ)).toNat := by
  unfold intHits natHits
  apply Finset.sum_congr rfl
  intro t _
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have hcast : ((((r-s)%(q:ℤ)).toNat:ℕ):ℤ)=(r-s)%(q:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
  have heq : Int.ModEq (q:ℤ) (s+(t:ℤ)) r ↔ t%q=((r-s)%(q:ℤ)).toNat := by
    constructor
    · intro h
      have h' := h.add_right (-s)
      have e : (s+(t:ℤ))+(-s)=(t:ℤ) := by ring
      have e' : r+(-s)=r-s := by ring
      rw [e,e'] at h'
      change ((t:ℤ)%(q:ℤ))=(r-s)%(q:ℤ) at h'
      rw [Int.ofNat_mod_ofNat,←hcast] at h'
      exact_mod_cast h'
    · intro h
      have hc := congrArg (fun z : ℕ => (z:ℤ)) h
      rw [←Int.ofNat_mod_ofNat,hcast] at hc
      have h' : Int.ModEq (q:ℤ) (t:ℤ) (r-s) := hc
      have ha := h'.add_left s
      convert ha using 1 <;> ring
  simp only [heq]

theorem exact_int_count (q L : ℕ) (s r : ℤ) (hq : 0<q) :
    intHits q L s r =
      L/q+(if ((r-s)%(q:ℤ)).toNat<L%q then 1 else 0) := by
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have hr := Int.emod_lt_of_pos (r-s) hqz
  have hr₀ := Int.emod_nonneg (r-s) hqz.ne'
  rw [int_eq_nat q L s r hq,exact_nat_count q L _ hq (by omega)]

theorem int_count_error (q L : ℕ) (s r : ℤ) (hq : 0<q) :
    |(intHits q L s r:ℝ)-(L:ℝ)/(q:ℝ)| ≤ 1 := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hdiv : (L:ℝ)/(q:ℝ)=((L/q:ℕ):ℝ)+((L%q:ℕ):ℝ)/(q:ℝ) := by
    have hz : (q:ℝ)*((L/q:ℕ):ℝ)+((L%q:ℕ):ℝ)=(L:ℝ) := by
      exact_mod_cast Nat.div_add_mod L q
    apply (div_eq_iff hqR.ne').2
    rw [add_mul,div_mul_cancel₀ _ hqR.ne']
    linarith
  have ht : ((L%q:ℕ):ℝ)/(q:ℝ)<1 := (div_lt_iff₀ hqR).mpr
    (by simpa only [one_mul] using (show ((L%q:ℕ):ℝ)<(q:ℝ) by exact_mod_cast Nat.mod_lt L hq))
  have ht₀ : 0≤((L%q:ℕ):ℝ)/(q:ℝ) := by positivity
  rw [hdiv,exact_int_count q L s r hq]
  split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;>
    linarith only [ht,ht₀]

end ActualTZResidueIntervalCount318
