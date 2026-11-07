module
public import QuarticOptimization
public import Mathlib.Algebra.Ring.Int.Parity
public section
namespace OddAffineInput
open QuarticOptimization

theorem odd_squarefree_affine_input (q : ℚ) (a : ℕ)
    (hsf : Squarefree a) (ha : Odd (a : ℤ)) :
    (∃ k : ℤ, Odd k ∧ (a : ℚ)*(2*q+1)^2=k) ↔
      ∃ z : ℤ, (z : ℚ)=q := by
  constructor
  · rintro ⟨k,hko,hk⟩
    obtain ⟨n,hn⟩ := squarefree_multiple_square_integral (2*q+1) a hsf k hk
    have hki : (a : ℤ)*n^2=k := by
      rw [←hn] at hk
      exact_mod_cast hk
    rw [←hki] at hko
    have hs : Odd (n*n) := by simpa [pow_two] using (Int.odd_mul.mp hko).2
    have ho : Odd n := (Int.odd_mul.mp hs).1
    obtain ⟨z,hz⟩ := ho.exists_bit1
    refine ⟨z, ?_⟩
    have hc : (n : ℚ)=2*(z : ℚ)+1 := by exact_mod_cast hz
    linarith
  · rintro ⟨z,rfl⟩
    have ho : Odd (2*z+1) := ⟨z,by ring⟩
    refine ⟨(a : ℤ)*(2*z+1)^2,ha.mul ho.pow,?_⟩
    push_cast
    ring

theorem multiplier_3723_squarefree : Squarefree (3723 : ℕ) := by
  intro d hd
  have hle : d*d ≤ 3723 := Nat.le_of_dvd (by decide) hd
  have hdle : d ≤ 61 := by nlinarith
  interval_cases d <;> norm_num at *

theorem odd_input_3723 (q : ℚ) :
    (∃ k : ℤ, Odd k ∧ 3723*(2*q+1)^2=k) ↔
      ∃ z : ℤ, (z : ℚ)=q := by
  simpa using odd_squarefree_affine_input q 3723 multiplier_3723_squarefree (by norm_num)

end OddAffineInput
