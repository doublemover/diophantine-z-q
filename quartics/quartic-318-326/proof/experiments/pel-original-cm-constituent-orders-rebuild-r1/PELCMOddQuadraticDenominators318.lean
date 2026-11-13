module
public import PELCMQuadraticIntegralTraceData318
public import Mathlib.Data.ZMod.Basic
public section
namespace PELCMOddQuadraticDenominators318
@[expose] def coefficient : Fin 3→ℤ := ![-1,1,-2]
@[expose] def discriminant (i:Fin 3) : ℤ := 4*coefficient i+1
lemma discriminant_nonzero (i:Fin 3) : discriminant i≠0 := by
  fin_cases i <;> norm_num [discriminant,coefficient]
lemma prime_dvd_U (p:ℕ) [Fact p.Prime] (d T U N:ℤ) (hd:(d:ZMod p)=0)
    (h:d*T^2-U^2=4*d*N) : (p:ℤ)∣U := by
  have hh := congrArg (Int.castRingHom (ZMod p)) h
  have he : (d:ZMod p)*(T:ZMod p)^2-(U:ZMod p)^2=4*(d:ZMod p)*(N:ZMod p) := by
    simpa using hh
  have hs : (U:ZMod p)^2=0 := by simpa [hd] using he
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd U p).mp (pow_eq_zero hs)
lemma discriminant_dvd_U (i:Fin 3) (T U N:ℤ)
    (h:discriminant i*T^2-U^2=4*discriminant i*N) : discriminant i∣U := by
  fin_cases i
  · letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hu := prime_dvd_U 3 (-3) T U N (by norm_num) (by simpa [discriminant,coefficient] using h)
    simpa [discriminant,coefficient] using hu
  · letI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hu := prime_dvd_U 5 5 T U N (by norm_num) (by simpa [discriminant,coefficient] using h)
    simpa [discriminant,coefficient] using hu
  · letI : Fact (Nat.Prime 7) := ⟨by decide⟩
    have hu := prime_dvd_U 7 (-7) T U N (by norm_num) (by simpa [discriminant,coefficient] using h)
    simpa [discriminant,coefficient] using hu
lemma parity_obstruction : ∀t s:ZMod 4,t^2-s^2=0 →
    ZMod.castHom (by decide:2∣4) (ZMod 2) (t-s)=0 := by decide
lemma parity (i:Fin 3) (T S N:ℤ)
    (h:T^2-discriminant i*S^2=4*N) : (2:ℤ)∣T-S := by
  have hh := congrArg (Int.castRingHom (ZMod 4)) h
  have he : (T:ZMod 4)^2-(S:ZMod 4)^2=0 := by
    fin_cases i <;> norm_num [discriminant,coefficient] at hh ⊢ <;> exact hh
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (T-S) 2).mp
    (by simpa using parity_obstruction (T:ZMod 4) (S:ZMod 4) he)
lemma coordinates (i:Fin 3) (T U N:ℤ)
    (h:discriminant i*T^2-U^2=4*discriminant i*N) :
    ∃r s:ℤ,U=discriminant i*s ∧ T=2*r+s := by
  obtain ⟨s,hs⟩ := discriminant_dvd_U i T U N h
  have hmul : discriminant i*(T^2-discriminant i*s^2-4*N)=0 := by
    rw [hs] at h
    linear_combination h
  have he : T^2-discriminant i*s^2=4*N := by
    have hh := (mul_eq_zero.mp hmul).resolve_left (discriminant_nonzero i)
    linear_combination hh
  obtain ⟨r,hr⟩ := parity i T s N he
  exact ⟨r,s,hs,by omega⟩
end PELCMOddQuadraticDenominators318
