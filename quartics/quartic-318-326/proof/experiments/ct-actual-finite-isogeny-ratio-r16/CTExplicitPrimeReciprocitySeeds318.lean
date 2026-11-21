module
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
public section

namespace CTExplicitPrimeReciprocitySeeds318

open ZMod

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- The odd contribution for (-1,p), or for (p,p), cancels the
literal dyadic correction from the same integer p. -/
theorem odd_minusOne_seed (hp : p≠2) : legendreSym p (-1)*χ₄ p = 1 := by
  rw [←legendreSym.at_neg_one hp,←pow_two]
  exact legendreSym.sq_one p (by norm_num : (((-1:ℤ):ZMod p))≠0)

/-- The two retained contributions on the actual rational pair (2,p). -/
theorem odd_two_seed (hp : p≠2) : legendreSym p 2*χ₈ p = 1 := by
  have hp0 : 2≤p := (Fact.out : Nat.Prime p).two_le
  have h2 : (2:ZMod p)≠0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  rw [←legendreSym.at_two hp,←pow_two]
  apply legendreSym.sq_one p
  show (((2:ℕ):ℤ):ZMod p)≠0
  simpa only [Int.cast_natCast] using h2

/-- Pairwise signed prime product, with the actual dyadic correction
(-1)^((p/2)*(q/2)) and the two opposite odd projections. -/
theorem distinct_odd_seed (hp : p≠2) (hq : q≠2) (hpq : p≠q) :
    (-1:ℤ)^(p/2*(q/2)) * legendreSym q p * legendreSym p q = 1 := by
  rw [mul_assoc,legendreSym.quadratic_reciprocity hp hq hpq,←mul_pow]
  norm_num

end CTExplicitPrimeReciprocitySeeds318

#print axioms CTExplicitPrimeReciprocitySeeds318.distinct_odd_seed
