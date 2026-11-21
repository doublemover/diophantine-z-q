module
public import ActualTZIntervalMarginal318
public section
noncomputable section
namespace ActualTZSignedAxisSupport318
open scoped BigOperators
open ActualTZIntervalMarginal318 ActualTZResidueIntervalCount318

variable {p : ℕ} [NeZero p]

def digit (s : ℤ) (t : ℕ) : ZMod p := ((s+(t:ℤ)):ℤ)

def atom (L : ℕ) (s : ℤ) (x : ZMod p) : ℚ≥0 :=
  (intHits p L s (x.val:ℤ):ℚ≥0)/(L:ℚ≥0)

def axis (L : ℕ) (s : ℤ) : Finset (ZMod p) :=
  if L<p then (Finset.range L).image (digit s) else Finset.univ

theorem digit_hit (s : ℤ) (t : ℕ) (x : ZMod p) :
    digit s t=x ↔ Int.ModEq (p:ℤ) (s+(t:ℤ)) (x.val:ℤ) := by
  rw [←ZMod.intCast_eq_intCast_iff]
  simp only [digit,Int.cast_natCast,ZMod.natCast_zmod_val]

private theorem digit_short (L : ℕ) (s : ℤ) (hL : L≤p) :
    Set.InjOn (digit (p:=p) s) ↑(Finset.range L) := by
  intro t ht u hu h
  have H := (ZMod.intCast_eq_intCast_iff (s+(t:ℤ)) (s+(u:ℤ)) p).1 h
  have H' := H.add_right (-s)
  have HE : (t:ℤ)≡(u:ℤ) [ZMOD (p:ℤ)] := by
    convert H' using 1 <;> ring
  change (t:ℤ)%(p:ℤ)=(u:ℤ)%(p:ℤ) at HE
  rw [Int.ofNat_mod_ofNat,Int.ofNat_mod_ofNat,
      Nat.mod_eq_of_lt ((Finset.mem_range.mp ht).trans_le hL),
      Nat.mod_eq_of_lt ((Finset.mem_range.mp hu).trans_le hL)] at HE
  exact_mod_cast HE

theorem axis_card (L : ℕ) (s : ℤ) : (axis (p:=p) L s).card=min L p := by
  classical
  unfold axis
  by_cases h : L<p
  · rw [if_pos h,Finset.card_image_of_injOn (digit_short L s h.le),Finset.card_range,min_eq_left h.le]
  · rw [if_neg h,Finset.card_univ,ZMod.card,min_eq_right (le_of_not_gt h)]

theorem atom_outside (L : ℕ) (s : ℤ) (x : ZMod p) (hx : x∉axis L s) : atom L s x=0 := by
  classical
  have hc : L<p := by
    by_contra h
    exact hx (by simp only [axis,if_neg h,Finset.mem_univ])
  have h0 : intHits p L s (x.val:ℤ)=0 := by
    unfold intHits
    apply Finset.sum_eq_zero
    intro t ht
    apply if_neg
    intro hh
    exact hx (by
      rw [axis,if_pos hc]
      exact Finset.mem_image.mpr ⟨t,ht,(digit_hit s t x).2 hh⟩)
  simp only [atom,h0,Nat.cast_zero,zero_div]

theorem digit_mem (L : ℕ) (s : ℤ) (t : Fin L) :
    digit (p:=p) s t.val∈axis L s := by
  classical
  unfold axis
  by_cases h : L<p
  · rw [if_pos h]
    exact Finset.mem_image.mpr ⟨t.val,Finset.mem_range.mpr t.isLt,rfl⟩
  · simp only [if_neg h,Finset.mem_univ]

theorem atom_sum (L : ℕ) (s : ℤ) (x : ZMod p) :
    atom L s x = ∑ t : Fin L,if digit s t.val=x then 1/(L:ℚ≥0) else 0 := by
  classical
  unfold atom intHits
  rw [Nat.cast_sum,Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ=>if digit s t=x then 1/(L:ℚ≥0) else 0) L]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : digit s t=x
  · simp only [if_pos h,if_pos ((digit_hit s t x).1 h),Nat.cast_one]
  · simp only [if_neg h,if_neg (fun h' => h ((digit_hit s t x).2 h')),Nat.cast_zero,zero_div]

/-- Actual near-uniform signed-axis probability: shorter than p is
injective, longer uses the exact interval atom and positivity. No
independence across different primes is asserted. -/
theorem atom_dominance (L : ℕ) (s : ℤ) (hL : 0<L) (x : ZMod p) :
    atom L s x≤2/((axis (p:=p) L s).card:ℚ≥0) := by
  have hp : 0<p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [axis_card]
  by_cases h : L<p
  · rw [min_eq_left h.le,atom]
    have H : intHits p L s (x.val:ℤ)≤1 := by
      rw [exact_int_count p L s _ hp,Nat.div_eq_of_lt h,zero_add]
      split_ifs <;> omega
    exact div_le_div_of_nonneg_right (by exact_mod_cast (H.trans (by omega : 1≤2)))
      (by positivity)
  · rw [min_eq_right (le_of_not_gt h),atom]
    have hCount : intHits p L s (x.val:ℤ)≤L/p+1 := by
      rw [exact_int_count p L s _ hp]
      split_ifs <;> omega
    have hProd : intHits p L s (x.val:ℤ)*p≤2*L := calc
      _ ≤ (L/p+1)*p := Nat.mul_le_mul_right p hCount
      _ = (L/p)*p+p := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ L+L := Nat.add_le_add (Nat.div_mul_le_self _ _) (le_of_not_gt h)
      _ = _ := by omega
    have hp' : (0:ℚ≥0)<p := by exact_mod_cast hp
    have hL' : (0:ℚ≥0)<L := by exact_mod_cast hL
    apply (div_le_div_iff₀ hL' hp').2
    exact_mod_cast hProd

end ActualTZSignedAxisSupport318
