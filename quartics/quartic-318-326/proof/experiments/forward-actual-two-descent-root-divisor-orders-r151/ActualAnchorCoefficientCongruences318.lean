module
public import AnchorLocalSquareProduction318
public section
namespace ActualAnchorCoefficientCongruences318
open AnchorLocalSquareProduction318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The exact reduced numerator of the actual radicand is 1 modulo 24.
The hypotheses are the already produced local depths of the actual ratio. -/
theorem coefficient_one_mod_twentyfour (r : ℚ) (hr : r≠0)
    (h2 : padicValRat 2 r=0) (h3 : 0≤padicValRat 3 r) :
    (3*r.num^2-2*(r.den:ℤ)^2)%24=1 := by
  have hn := unit_two_num_odd r hr h2
  have hd2N := denominator_unit 2 r (by omega)
  have hd2 : ¬(2:ℤ)∣(r.den:ℤ) := by exact_mod_cast hd2N
  rw [Int.dvd_iff_emod_eq_zero] at hd2
  have hdodd : Odd (r.den:ℤ) := Int.odd_iff.mpr (by omega)
  have hn8 := odd_square_mod_eight _ hn
  have hd8 := odd_square_mod_eight _ hdodd
  have hd3N := denominator_unit 3 r h3
  have hd3 : ¬(3:ℤ)∣(r.den:ℤ) := by exact_mod_cast hd3N
  rw [Int.dvd_iff_emod_eq_zero] at hd3
  have hd3sq : (r.den:ℤ)^2%3=1 := by
    have hlo := Int.emod_nonneg (r.den:ℤ) (by norm_num : (3:ℤ)≠0)
    have hhi := Int.emod_lt_of_pos (r.den:ℤ) (by norm_num : (0:ℤ)<3)
    rw [show (r.den:ℤ)^2%3=((r.den:ℤ)%3)^2%3 by simp [pow_two,Int.mul_emod]]
    interval_cases he : (r.den:ℤ)%3 <;> norm_num at * <;> omega
  omega

/-- Removing any integral square factor preserves the signed residue 1 mod24.
No positivity of the remaining coefficient is assumed. -/
theorem square_factor_one_mod_twentyfour (e d : ℤ)
    (h : (e^2*d)%24=1) : d%24=1 := by
  have hlo := Int.emod_nonneg e (by norm_num : (24:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos e (by norm_num : (0:ℤ)<24)
  have he : e^2%24=(e%24)^2%24 := by simp [pow_two,Int.mul_emod]
  rw [Int.mul_emod,he] at h
  interval_cases hx : e%24 <;> norm_num [hx] at h <;> omega

/-- Every prime of the normalized coefficient splits 6. The root is the
literal reduced-ratio expression 3*num/den, not a chosen local-global witness. -/
theorem normalized_prime_splits_six (r : ℚ) (e d : ℤ)
    (he : e^2*d=3*r.num^2-2*(r.den:ℤ)^2) (hd : d%24=1)
    (p : ℕ) [Fact p.Prime] (hpd : (p:ℤ)∣d) : IsSquare (6 : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp3 : p≠3 := by
    intro h
    subst p
    have hh := Int.dvd_iff_emod_eq_zero.mp hpd
    omega
  have hthree : (3:ZMod p)≠0 := by
    intro h
    have hh : p∣3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    exact hp3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp hh |>.resolve_left hp.ne_one)
  have hd0 : (d:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd
  have hpoly : (3:ZMod p)*(r.num:ZMod p)^2-2*(r.den:ZMod p)^2=0 := by
    have hh := congrArg (fun n : ℤ => (n:ZMod p)) he
    push_cast at hh
    simpa only [hd0,mul_zero] using hh.symm
  have hb : (r.den:ZMod p)≠0 := by
    intro h
    have hnumprod : (3:ZMod p)*(r.num:ZMod p)^2=0 := by simpa [h] using hpoly
    have hnump : (r.num:ZMod p)*(r.num:ZMod p)=0 := by
      simpa only [pow_two] using (mul_eq_zero.mp hnumprod).resolve_left hthree
    have hnum : (r.num:ZMod p)=0 := (mul_eq_zero.mp hnump).elim id id
    have hnumZ := (ZMod.intCast_zmod_eq_zero_iff_dvd r.num p).mp hnum
    have hnumN : p∣r.num.natAbs := by
      simpa using (Int.natAbs_dvd_natAbs.mpr hnumZ)
    have hdenN : p∣r.den := (ZMod.natCast_eq_zero_iff r.den p).mp h
    have hg : r.num.natAbs.gcd r.den=1 := r.reduced
    have hh := Nat.dvd_gcd hnumN hdenN
    rw [hg] at hh
    exact hp.not_dvd_one hh
  have hs : (((3:ZMod p)*(r.num:ZMod p))/(r.den:ZMod p))^2=6 := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hb)).mpr
    linear_combination 3*hpoly
  exact ⟨(3:ZMod p)*(r.num:ZMod p)/(r.den:ZMod p),by simpa only [pow_two] using hs.symm⟩

/-- This congruence is instantiated at the actual fixed-label ratio without
assuming a rational anchor or a local-global principle. -/
theorem prepared_coefficient_one_mod_twentyfour (a : ℤ) (A B N d : ℕ) (hd : d≠0) :
    let ns := FixedArithmeticLabels318.labels a A B
      (PreparedAnchorLabels318.multiplier N d) (PreparedAnchorLabels318.multiplier_ne N d hd)
    let r := ActualAnchorRatio318.ratio ns N
    (3*r.num^2-2*(r.den:ℤ)^2)%24=1 := by
  dsimp only
  have hh := PreparedAnchorLabels318.actual_anchor_depths a A B N d hd
  exact coefficient_one_mod_twentyfour _ hh.1 hh.2.1 hh.2.2

end ActualAnchorCoefficientCongruences318
