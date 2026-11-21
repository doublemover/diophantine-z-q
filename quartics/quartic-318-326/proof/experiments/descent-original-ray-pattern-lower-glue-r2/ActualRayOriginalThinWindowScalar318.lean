module
public import Mathlib
public section
noncomputable section
namespace ActualRayOriginalThinWindowScalar318

/-- Exact same N margin for the shear and every genuine output.
A tolerance of N/32 leaves room for one full wheel digit on
each boundary. No prime or residue-unit input is needed. -/
theorem bounds (N W U V B τ D : ℝ)
    (hN : 0 ≤ N) (hW : 16*W ≤ N) (hV : 0 ≤ V)
    (hVB : V ≤ τ*B) (hτB : 0 ≤ τ*B) (hB : B^2 = N)
    (hU : (5/8:ℝ)*(N-W) ≤ U ∧ U ≤ (3/4:ℝ)*N+W)
    (hD : |D|*τ^2 ≤ 1/32) :
    N ≤ 2*(U+D*V^2) ∧ U+D*V^2 ≤ N := by
  have hv2 := pow_le_pow_left₀ hV hVB 2
  rw [mul_pow,hB] at hv2
  have hC : |D*V^2| ≤ N/32 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg V)]
    calc
      |D|*V^2 ≤ |D|*(τ^2*N) := mul_le_mul_of_nonneg_left hv2 (abs_nonneg _)
      _ = (|D|*τ^2)*N := by ring
      _ ≤ (1/32:ℝ)*N := mul_le_mul_of_nonneg_right hD hN
      _ = N/32 := by ring
  have hlo := (abs_le.mp hC).1
  have hhi := (abs_le.mp hC).2
  exact ⟨by linarith only [hW,hU.1,hlo,hN],by linarith only [hW,hU.2,hhi,hN]⟩

/-- Coarse step below T, with the actual subtract-one convention.
Includes exact divisibility T by W and c=0. -/
theorem step_upper (W T m c : ℕ) (hW : 0 < W) (hm : m ≤ T/W-1) (hmp : 0 < m)
    (hc : c < W) :
    1 ≤ W*m+c ∧ W*m+c ≤ T := by
  have hm' : m+1 ≤ T/W := by omega
  have hq : W*(T/W) ≤ T := by
    have h := Nat.mod_add_div T W
    omega
  have hh := (Nat.mul_le_mul_left W hm').trans hq
  rw [Nat.mul_add,Nat.mul_one] at hh
  exact ⟨by have := Nat.mul_pos hW hmp; omega,by omega⟩

end ActualRayOriginalThinWindowScalar318
