module
public import Height13RealLog
public import Mathlib.Data.ZMod.Basic
public section
namespace ShellDivisibility

/-- Phase-stripped good-prime recurrence, with b₀=1. -/
def b (a p kappa : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a-kappa
  | n+2 => a*b a p kappa (n+1)-p*b a p kappa n

/-- At the unramified squarefree input, the divided-shell numerator has
    the same residue modulo four at every shell. -/
theorem split_shell_mod_four (a p kappa : ℤ)
    (ha : (a : ZMod 4) = p+1)
    (hp : (p : ZMod 4) = 1 ∨ (p : ZMod 4) = 3)
    (hk : kappa = 1 ∨ kappa = -1) (n : ℕ) :
    ((b a p kappa (n+1)-b a p kappa n : ℤ) : ZMod 4) = a-kappa-1 := by
  have hd : (p : ZMod 4) * (a-kappa-1) = a-kappa-1 := by
    rcases hp with hp | hp <;> rcases hk with hk | hk <;>
      subst kappa <;> rw [ha, hp] <;> norm_num <;> decide
  induction n with
  | zero => simp [b]
  | succ n ih =>
    calc
      ((b a p kappa (n+1+1)-b a p kappa (n+1) : ℤ) : ZMod 4)
          = (p : ZMod 4) * ((b a p kappa (n+1)-b a p kappa n : ℤ) : ZMod 4) := by
              simp only [b, Int.cast_sub, Int.cast_mul]
              rw [ha]
              ring
      _ = a-kappa-1 := by rw [ih, hd]

/-- The modular congruence entails actual integer-two divisibility; it is
    not division of a residue-field equality by zero. -/
theorem split_shell_even (a p kappa : ℤ)
    (ha : (a : ZMod 4) = p+1)
    (hp : (p : ZMod 4) = 1 ∨ (p : ZMod 4) = 3)
    (hk : kappa = 1 ∨ kappa = -1) (n : ℕ) :
    2 ∣ b a p kappa (n+1)-b a p kappa n := by
  have hm := split_shell_mod_four a p kappa ha hp hk n
  have hzero : ((b a p kappa (n+1)-b a p kappa n : ℤ) : ZMod 4) = 0 ∨
      ((b a p kappa (n+1)-b a p kappa n : ℤ) : ZMod 4) = 2 := by
    rcases hp with hp | hp <;> rcases hk with hk | hk <;>
      subst kappa <;> rw [hm, ha, hp] <;> norm_num <;> decide
  rcases hzero with h | h
  · have hd : (4 : ℤ) ∣ b a p kappa (n+1)-b a p kappa n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h
    exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) hd
  · have hz : ((b a p kappa (n+1)-b a p kappa n - 2 : ℤ) : ZMod 4) = 0 := by
      rw [Int.cast_sub, h]; norm_num
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hz
    obtain ⟨v,hv⟩ := hd
    use 2*v+1
    omega

/-- After proving divisibility over the integers, division by two sends
    congruence modulo four to congruence modulo two. -/
theorem divide_actual_two (x y : ℤ) (hx : 2 ∣ x) (hy : 2 ∣ y)
    (hxy : (x : ZMod 4) = (y : ZMod 4)) :
    (x/2 : ℤ) % 2 = (y/2 : ℤ) % 2 := by
  have hc := (ZMod.intCast_eq_intCast_iff x y 4).mp hxy
  change x % 4 = y % 4 at hc
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  omega

/-- The literal O.10 quotient, as an equality of integer residues. -/
theorem divided_shell_constant (a p kappa : ℤ)
    (ha : (a : ZMod 4) = p+1)
    (hp : (p : ZMod 4) = 1 ∨ (p : ZMod 4) = 3)
    (hk : kappa = 1 ∨ kappa = -1) (n : ℕ) :
    ((b a p kappa (n+1)-b a p kappa n)/2) % 2 = ((a-kappa-1)/2) % 2 := by
  apply divide_actual_two
  · exact split_shell_even a p kappa ha hp hk n
  · simpa [b] using split_shell_even a p kappa ha hp hk 0
  · simpa using split_shell_mod_four a p kappa ha hp hk n

/-- The ordinary shell factors outside U are odd on unary indices.
    This is used before reduction to the ramified residue field. -/
theorem split_coefficient_odd (a p kappa : ℤ)
    (ha : (a : ZMod 4) = p+1)
    (hp : (p : ZMod 4) = 1 ∨ (p : ZMod 4) = 3)
    (hk : kappa = 1 ∨ kappa = -1) (n : ℕ) :
    ((b a p kappa n : ℤ) : ZMod 2) = 1 := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (b a p kappa (n+1)-b a p kappa n) 2).mpr
        (split_shell_even a p kappa ha hp hk n)
    rw [Int.cast_sub, sub_eq_zero] at hz
    exact hz.trans ih

/-- At p dividing the originating squarefree parameter, every shell
    difference is an integer unit modulo two. The s=0 endpoint is b₀−b₋₁=1. -/
theorem ramified_shell_odd (a p : ℤ)
    (ha : (a : ZMod 2) = 0) (hp : (p : ZMod 2) = 1) (n : ℕ) :
    ((b a p 0 (n+1)-b a p 0 n : ℤ) : ZMod 2) = 1 := by
  have hc : ∀ x y : ZMod 2, -x-y=y-x := by decide
  induction n with
  | zero => simp [b, ha]
  | succ n ih =>
    calc
      ((b a p 0 (n+1+1)-b a p 0 (n+1) : ℤ) : ZMod 2)
          = ((b a p 0 (n+1)-b a p 0 n : ℤ) : ZMod 2) := by
            simp only [b, Int.cast_sub, Int.cast_mul]
            rw [ha, hp, zero_mul, one_mul, zero_sub, hc]
      _ = 1 := ih

/-- The opposite Legendre signs in whole-prime omission flip the divided
    integer coefficient by one in F₂, regardless of the sign orientation. -/
theorem opposite_sign_divided_sum (a : ℤ) (ha : 2 ∣ a) :
    (((a-1-1)/2 + (a+1-1)/2 : ℤ) : ZMod 2) = 1 := by
  obtain ⟨v,hv⟩ := ha
  have hs : (a-1-1)/2 + (a+1-1)/2 = 2*v-1 := by omega
  rw [hs]
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2]
  norm_num
  decide

#print axioms split_shell_mod_four
#print axioms split_shell_even
#print axioms divide_actual_two
#print axioms divided_shell_constant
#print axioms split_coefficient_odd
#print axioms ramified_shell_odd
#print axioms opposite_sign_divided_sum
end ShellDivisibility

