module
public import ActualTwoDescentFiniteEllipticModel318
public section
noncomputable section
namespace ActualTwoDescentFiniteHalvingRoots318
open ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [NeZero (2 : K)] [NeZero (3 : K)]

/-- The identity Kummer class supplies all three actual square roots with
the product sign required by the halving formula. -/
theorem actual_halving_roots (n x y : K) (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) (H : SquarePair (x+3*n) (x-n) 1 1) :
    ∃ a b c : K, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      a^2=x ∧ b^2=x-n ∧ c^2=x+3*n ∧ a*b*c= -y := by
  obtain ⟨c,b,hc0,hb0,hc2,hb2⟩ := H
  simp only [one_mul] at hc2 hb2
  have hy : y ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    exact (mul_ne_zero (mul_ne_zero hx hB) hA) hc.symm
  let a := -y/(b*c)
  refine ⟨a,b,c,div_ne_zero (neg_ne_zero.mpr hy) (mul_ne_zero hb0 hc0),hb0,hc0,?_,hb2.symm,hc2.symm,?_⟩
  · dsimp [a]
    rw [div_pow,neg_sq,mul_pow,hc,←hb2,←hc2]
    field_simp [hA,hB]
    <;> ring
  · dsimp [a]
    field_simp [hb0,hc0]
    <;> ring

end ActualTwoDescentFiniteHalvingRoots318
