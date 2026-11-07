module
public import LucasHeight318
public section
namespace LucasSequence318

/-- The integral Lucas sequence attached to X²-aX+1. -/
@[expose] def U (a : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => a * U a (n+1) - U a n

@[simp] theorem U_zero (a : ℤ) : U a 0 = 0 := rfl
@[simp] theorem U_one (a : ℤ) : U a 1 = 1 := rfl
 theorem U_next (a : ℤ) (n : ℕ) : U a (n+2) = a*U a (n+1)-U a n := rfl

 theorem U_growth (a : ℤ) (ha : 3 ≤ a) (n : ℕ) :
    0 ≤ U a n ∧ U a n < U a (n+1) ∧ (a-1)^n ≤ U a (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : 1 ≤ U a (n+1) := by omega
    have hm : (a-1)*U a (n+1) ≤ U a (n+2) := by
      rw [U_next]
      nlinarith only [ih.2.1]
    have hmono : U a (n+1) < U a (n+2) := by
      have := mul_le_mul_of_nonneg_right (show 2 ≤ a-1 by omega) (show 0 ≤ U a (n+1) by omega)
      nlinarith only [this, hm, hu]
    refine ⟨by omega, hmono, ?_⟩
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih.2.2 (by omega)).trans (by simpa [mul_comm] using hm)

/-- Every ordered nonnegative solution is a consecutive Lucas pair. This is
an integer Vieta descent, so no unproved unit-generation assertion is used. -/
theorem ordered_solution (a : ℤ) (ha : 3 ≤ a) (y : ℕ) :
    ∀ x : ℕ, x < y → (x:ℤ)^2-a*x*y+y^2=1 →
      ∃ n : ℕ, U a n=x ∧ U a (n+1)=y := by
  induction y using Nat.strong_induction_on with
  | h y ih =>
    intro x hxy heq
    by_cases hx : x=0
    · subst x
      have hy : y=1 := by norm_num at heq; nlinarith
      subst y
      exact ⟨0,rfl,rfl⟩
    have hxpos : (0:ℤ)<x := by exact_mod_cast Nat.pos_of_ne_zero hx
    have hypos : (0:ℤ)<y := by exact_mod_cast (Nat.zero_le x).trans_lt hxy
    have hxyZ : (x:ℤ)<y := by exact_mod_cast hxy
    let z : ℤ := a*x-y
    have hprod : (y:ℤ)*z=(x:ℤ)^2-1 := by dsimp [z]; nlinarith only [heq]
    have hz : 0≤z := by
      by_contra hn
      have hzneg : z≤-1 := by omega
      have := mul_le_mul_of_nonneg_left hzneg (show (0:ℤ)≤y by omega)
      nlinarith only [hprod, this, hxpos, hypos]
    have hzx : z<x := by
      by_contra hn
      have hge : (x:ℤ)≤z := by omega
      have := mul_le_mul_of_nonneg_left hge (show (0:ℤ)≤y by omega)
      have hprodxy : (x:ℤ)^2 < y*x := by nlinarith only [hxyZ,hxpos]
      nlinarith only [this,hprod,hprodxy]
    have hzcast : (z.toNat:ℤ)=z := Int.toNat_of_nonneg hz
    have hzxN : z.toNat<x := by exact_mod_cast (show (z.toNat:ℤ)<x by omega)
    have hnew : (z.toNat:ℤ)^2-a*z.toNat*x+x^2=1 := by
      rw [hzcast]
      dsimp [z]
      nlinarith only [heq]
    obtain ⟨n,hn0,hn1⟩ := ih x hxy z.toNat hzxN hnew
    refine ⟨n+1,hn1,?_⟩
    rw [show n+1+1=n+2 by omega,U_next,hn1,hn0,hzcast]
    dsimp [z]
    ring

/-- The recurrence is congruent to the index modulo a-2. -/
theorem mod_minus (a : ℤ) (n : ℕ) : a-2 ∣ U a n-n := by
  have hp : ∀ n : ℕ, (a-2 ∣ U a n-n) ∧ (a-2 ∣ U a (n+1)-(n+1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := dvd_add (dvd_sub (dvd_mul_of_dvd_left ih.2 a) ih.1)
        (dvd_mul_right (a-2) ((n:ℤ)+1))
      convert h using 1 <;> rw [U_next] <;> push_cast <;> ring
  exact (hp n).1

/-- Modulo a+2 the sequence is the alternating index. -/
theorem mod_plus (a : ℤ) (n : ℕ) : a+2 ∣ (-1:ℤ)^n * U a n+n := by
  have hp : ∀ n : ℕ, (a+2 ∣ (-1:ℤ)^n*U a n+n) ∧
      (a+2 ∣ (-1:ℤ)^(n+1)*U a (n+1)+(n+1)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := dvd_add (dvd_sub (dvd_mul_of_dvd_left ih.2 (-a)) ih.1)
        (dvd_mul_right (a+2) ((n:ℤ)+1))
      convert h using 1 <;> rw [U_next] <;> push_cast <;> simp only [pow_succ] <;> ring
  exact (hp n).1

end LucasSequence318
