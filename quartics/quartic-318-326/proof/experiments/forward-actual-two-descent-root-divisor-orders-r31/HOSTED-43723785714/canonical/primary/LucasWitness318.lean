module
public import LucasDivisibility318
public section
namespace LucasSequence318

/-- The consecutive Lucas terms satisfy the actual norm equation. -/
theorem U_norm (a : ℤ) (n : ℕ) :
    U a (n+1)^2-a*U a (n+1)*U a n+U a n^2=1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,U_next]
    nlinarith only [ih]

/-- A prescribed multiple of the index modulus yields a positive integral
Lucas solution. This permits taking the index arbitrarily far out. -/
theorem positive_witness_at_index (s : ℤ) (hs : 3≤ |s|) (k : ℕ)
    (hk : 0<k) (hdiv : |s-2| ∣ (k:ℤ)) :
    ∃ t z : ℤ, 0<t ∧ 0<z ∧ t=U |s| (k+1) ∧
      |s-2| * z=U |s| k ∧ t^2-s*(s-2)*t*z+(s-2)^2*z^2=1 := by
  have hd : |s-2|=|s|-2 ∨ |s-2|=|s|+2 := by
    rcases le_total 0 s with h|h
    · left; rw [abs_of_nonneg h] at hs ⊢; rw [abs_of_nonneg (by omega)]
    · right; rw [abs_of_nonpos h,abs_of_nonpos (by omega)]; ring
  have hdpos : 0< |s-2| := by rcases hd with h|h <;> omega
  have huDiv : |s-2| ∣ U |s| k := by
    rcases hd with hd|hd
    · have h := dvd_add (hd ▸ mod_minus |s| k) hdiv
      simpa only [sub_add_cancel] using h
    · have h := dvd_sub (hd ▸ mod_plus |s| k) hdiv
      have hm : |s-2| ∣ (-1:ℤ)^k*U |s| k := by simpa only [add_sub_cancel_right] using h
      have hp : IsUnit ((-1:ℤ)^k) := isUnit_neg_one.pow k
      exact (hp.dvd_mul_left).mp hm
  obtain ⟨z,hz⟩ := huDiv
  have huk : 0<U |s| k := by
    have h := (U_growth |s| hs (k-1)).2.1
    rw [Nat.sub_add_cancel hk] at h
    exact (U_growth |s| hs (k-1)).1.trans_lt h
  have hzpos : 0<z := by nlinarith only [hz,huk,hdpos]
  have htpos := huk.trans (U_growth |s| hs k).2.1
  have hcoeff : |s| * |s-2|=s*(s-2) := by
    rcases le_total 0 s with h|h
    · rw [abs_of_nonneg h] at hs ⊢
      rw [abs_of_nonneg (by omega)]
    · rw [abs_of_nonpos h,abs_of_nonpos (by omega)]
      ring
  refine ⟨U |s| (k+1),z,htpos,hzpos,rfl,hz.symm,?_⟩
  have hn := U_norm |s| k
  rw [hz] at hn
  have hsq : |s-2|^2=(s-2)^2 := sq_abs _
  nlinarith only [hn,congrArg (fun x:ℤ => x*U |s| (k+1)*z) hcoeff,
    congrArg (fun x:ℤ => x*z^2) hsq]

/-- Every parameter in the range used by the source has positive integral
witnesses for its literal Lucas equation. -/
theorem positive_witness (s : ℤ) (hs : 3≤ |s|) :
    ∃ t z : ℤ, 0<t ∧ 0<z ∧ t^2-s*(s-2)*t*z+(s-2)^2*z^2=1 := by
  have hs2 : s-2≠0 := by
    intro h
    have : s=2 := by omega
    norm_num [this] at hs
  have hk : 0<(s-2).natAbs := Int.natAbs_pos.mpr hs2
  obtain ⟨t,z,ht,hz,_,_,heq⟩ := positive_witness_at_index s hs (s-2).natAbs hk (by simp)
  exact ⟨t,z,ht,hz,heq⟩

/-- For odd parameters, the exact parity period is 0,1,1. -/
theorem U_mod_two (a : ℤ) (ha : Odd a) (n : ℕ) :
    U a n % 2 = if n%3=0 then 0 else 1 := by
  have ha2 : a%2=1 := Int.odd_iff.mp ha
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
    rw [U_next,Int.sub_emod,Int.mul_emod,ha2,hn,hn1]
    omega

/-- At indices congruent to one modulo three, both literal witnesses are
odd. This is the parity choice used by source completeness. -/
theorem positive_odd_witness_at_index (s : ℤ) (hs : 3≤ |s|) (hsodd : Odd s)
    (k : ℕ) (hk : 0<k) (hdiv : |s-2| ∣ (k:ℤ)) (hk3 : k%3=1) :
    ∃ t z : ℤ, 0<t ∧ 0<z ∧ Odd t ∧ Odd z ∧
      t^2-s*(s-2)*t*z+(s-2)^2*z^2=1 := by
  obtain ⟨t,z,ht,hz,hteq,hzeq,heq⟩ := positive_witness_at_index s hs k hk hdiv
  have hsa : Odd |s| := by
    rcases le_total 0 s with h|h
    · simpa only [abs_of_nonneg h] using hsodd
    · simpa only [abs_of_nonpos h] using hsodd.neg
  have huk : Odd (U |s| k) := Int.odd_iff.mpr (by rw [U_mod_two |s| hsa k]; simp [hk3])
  have htk : Odd (U |s| (k+1)) := Int.odd_iff.mpr (by
    rw [U_mod_two |s| hsa (k+1)]
    have h : (k+1)%3=2 := by omega
    simp [h])
  refine ⟨t,z,ht,hz,hteq ▸ htk,?_,heq⟩
  exact Int.Odd.of_mul_right (hzeq ▸ huk)

/-- The concrete index 2(s−2) used in source completeness gives positive odd
witnesses whenever s is odd, s≥3 and s≡1 modulo three. -/
theorem source_positive_odd_witness (s : ℤ) (hs : 3≤s) (hsodd : Odd s)
    (hs3 : s%3=1) :
    ∃ t z : ℤ, 0<t ∧ 0<z ∧ Odd t ∧ Odd z ∧
      t^2-s*(s-2)*t*z+(s-2)^2*z^2=1 := by
  have hd : (0:ℤ)<s-2 := by omega
  have hcast : ((s-2).natAbs:ℤ)=s-2 := by simp [abs_of_pos hd]
  have hk : 0<2*(s-2).natAbs := by exact Nat.mul_pos (by omega) (Int.natAbs_pos.mpr hd.ne')
  have hdiv : |s-2| ∣ (2*(s-2).natAbs:ℕ) := by
    push_cast
    exact dvd_mul_left _ _
  have hk3 : (2*(s-2).natAbs)%3=1 := by
    have hcast3 : ((s-2).natAbs:ℤ)%3=2 := by rw [hcast]; omega
    have hd3 : (s-2).natAbs%3=2 := by exact_mod_cast hcast3
    omega
  exact positive_odd_witness_at_index s (by rw [abs_of_nonneg (by omega)]; exact hs)
    hsodd (2*(s-2).natAbs) hk hdiv hk3

end LucasSequence318
