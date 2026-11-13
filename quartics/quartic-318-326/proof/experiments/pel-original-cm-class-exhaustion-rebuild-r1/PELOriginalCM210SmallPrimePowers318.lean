module
public import PELOriginalCM210NativeClassProductRelation318
public section
namespace PELOriginalCM210SmallPrimePowers318
lemma base_le_power (p n:ℕ) (hp:0<p) (hn:0<n) : p≤p^n := by
  cases n with
  | zero => omega
  | succ n =>
    have hpos : 0<p^n := pow_pos hp n
    have h : 1≤p^n := by omega
    rw [pow_succ]
    simpa only [one_mul] using Nat.mul_le_mul_right p h
lemma small_prime (p:ℕ) (hp:p.Prime) (h:p≤18) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 := by
  interval_cases p <;> norm_num at hp ⊢
lemma large_exponent_one (p n:ℕ) (hp:11≤p) (hn:0<n) (h:p^n≤18) : n=1 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hpos : 0<p^n := pow_pos (by omega) n
      simp only [pow_succ] at h
      have hsq : p*p≤p^n*p*p := by
        have h1 : 1≤p^n := by omega
        simpa only [one_mul] using Nat.mul_le_mul_right p (Nat.mul_le_mul_right p h1)
      nlinarith
end PELOriginalCM210SmallPrimePowers318
