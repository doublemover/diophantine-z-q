module
public import LegendrePadicPrimitiveResidues318
public import LegendrePrimitiveModularRoot318
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public section
namespace LocalNormPrimeSplitting318

/-- A genuine local norm of an integer with exactly one p-factor forces
the defining coefficient to be a square modulo p. Primitive integral data
are constructed by the checked Qp residue theorem, not assumed. -/
theorem square_of_local_odd_factor (p : ℕ) [Fact p.Prime]
    (a B : ℤ) (hB : ¬(p:ℤ)∣B) (x z : ℚ_[p])
    (hnorm : z^2-(a:ℚ_[p])*x^2=(((p:ℤ)*B:ℤ):ℚ_[p])) :
    IsSquare (a:ZMod p) := by
  have hsol : z^2-(a:ℚ_[p])*x^2-(((p:ℤ)*B:ℤ):ℚ_[p])*(1:ℚ_[p])^2=0 := by
    simpa only [one_pow,mul_one] using sub_eq_zero.mpr hnorm
  obtain ⟨X,Z,W,hcong,hprim⟩ :=
    LegendrePadicPrimitiveResidues318.residues_of_local_solution
      p a ((p:ℤ)*B) x z 1 (by simp) hsol
  exact LegendrePrimitiveModularRoot318.square_of_primitive_mod_square
    p a B X Z W hB hcong hprim

/-- Thus every odd prime occurring exactly once in a square-normalized,
locally represented integer splits2. This is the actual local-to-symbol step for the selected
auxiliary integer, without an unramified-extension theorem as a premise. -/
theorem jacobi_two_of_local_odd_factor (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (B : ℤ) (hB : ¬(p:ℤ)∣B) (x z : ℚ_[p])
    (hnorm : z^2-2*x^2=(((p:ℤ)*B:ℤ):ℚ_[p])) :
    jacobiSym 2 p=1 := by
  have hp : p.Prime := Fact.out
  have hnot : ¬p∣2 := by
    intro hd
    exact hp2 ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left hp.ne_one)
  have htwo : (2:ZMod p)≠0 := fun h => hnot ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hs := square_of_local_odd_factor p 2 B hB x z (by simpa using hnorm)
  rw [←legendreSym.to_jacobiSym p 2]
  exact (legendreSym.eq_one_iff p (by simpa using htwo)).mpr hs

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- In particular the selected integer cannot contain exactly one factor3.
The parity restriction may be proved after finite approximation, rather than
assumed when choosing its Dirichlet residue class. -/
theorem no_three_odd_factor (B : ℤ) (hB : ¬(3:ℤ)∣B)
    (x z : ℚ_[3]) (hnorm : z^2-2*x^2=((3*B:ℤ):ℚ_[3])) : False := by
  have hs := square_of_local_odd_factor 3 2 B hB x z (by simpa using hnorm)
  obtain ⟨r,hr⟩ := hs
  fin_cases r <;> norm_num at hr

end LocalNormPrimeSplitting318
