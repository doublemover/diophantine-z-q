module
public import ActualTwoDescentRepresentedSupport318
public section
noncomputable section
namespace ActualTwoDescentRepresentedThree318
open ActualTwoDescentRepresentedSupport318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentThreeAdicSecondSquare318 ActualTwoDescentUnitSquareNecessity318
open ActualTwoDescentLiteralUnitData318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Genuine local representation at3 produces the literal Jacobi condition
on the positive second representative. The nonzero square multiplier is
canceled against the square root derived from the ACTUAL cubic. -/
theorem actual_represented_three (n M L : ℕ) (hn : (n : ZMod 3)=2)
    (hL : Nat.Coprime L 3) (H : RepresentedAt 3 n M L) : jacobiSym (L : ℤ) 3=1 := by
  obtain ⟨P,r,v,hr,hv,hA,hB⟩ := H
  obtain ⟨s,hs,he⟩ := actual_three_second_square n hn P
  have hroot : (s/v)^2=((L : ℤ) : ℚ_[3]) := by
    rw [div_pow,he,hB]
    push_cast
    field_simp [hv]
  exact actual_unit_square_symbol (L : ℤ) (actual_nat_int_coprime L 3 hL) _ hroot

lemma actual_monomial_coprime_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp3 : ∀ i, p i ≠ 3)
    (v : ι → ZMod 2) : Nat.Coprime (monomial p v) 3 := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i _
  apply Nat.Coprime.pow_left
  exact (Nat.coprime_primes Fact.out (by decide : Nat.Prime 3)).mpr (hp3 i)

end ActualTwoDescentRepresentedThree318
