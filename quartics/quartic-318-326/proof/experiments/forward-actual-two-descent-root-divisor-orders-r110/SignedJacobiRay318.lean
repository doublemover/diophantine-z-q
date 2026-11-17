module
public import FiniteRayRootAlgebra318
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public section
noncomputable section
namespace SignedJacobiRay318
open ZMod
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

lemma jacobi_congr (a b : ℤ) (q : ℕ) (hd : (q:ℤ)∣b-a) :
    jacobiSym a q=jacobiSym b q :=
  jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr hd)

lemma prime_symbol_cases (q : ℕ) (hq0 : 0<q) (hqp : q<p) :
    jacobiSym (p:ℤ) q=1 ∨ jacobiSym (p:ℤ) q= -1 := by
  have hcop : p.Coprime q := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
    intro hd
    exact not_le_of_gt hqp (Nat.le_of_dvd hq0 hd))
  apply jacobiSym.eq_one_or_neg_one
  change Nat.gcd p q=1
  exact hcop.gcd_eq_one

lemma nat_residue_ne (q : ℕ) (hq0 : 0<q) (hqp : q<p) : (q:ZMod p)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff q p).mp hz
  exact not_le_of_gt hqp (Nat.le_of_dvd hq0 hd)

lemma int_residue_ne (a : ℤ) (ha0 : 0<a.natAbs) (hap : a.natAbs<p) : (a:ZMod p)≠0 := by
  have hn := nat_residue_ne p a.natAbs ha0 hap
  by_cases ha : 0≤a
  · have he : (a:ZMod p)=(a.natAbs:ZMod p) := by
      exact_mod_cast ((Int.natCast_natAbs a).trans (abs_of_nonneg ha)).symm
    rwa [he]
  · have he : (a:ZMod p)= -(a.natAbs:ZMod p) := by
      have hh : (a.natAbs:ℤ)= -a := by rw [Int.natCast_natAbs,abs_of_neg (by omega)]
      exact_mod_cast (show a= -(a.natAbs:ℤ) by omega)
    rw [he,neg_ne_zero]
    exact hn

/-- Signed integer numerator and absolute-value denominator are connected
explicitly; p≡1 mod4 makes the negative sign a square. -/
theorem square_from_reciprocity (hp4 : p%4=1) (a : ℤ)
    (ha0 : 0<a.natAbs) (hap : a.natAbs<p) (haodd : Odd a.natAbs)
    (hJ : jacobiSym (p:ℤ) a.natAbs=1) : IsSquare (a:ZMod p) := by
  have hrec := jacobiSym.quadratic_reciprocity_one_mod_four hp4 haodd
  have hj : jacobiSym (a.natAbs:ℤ) p=1 := hrec.symm.trans hJ
  have hs : IsSquare (a.natAbs:ZMod p) := (legendreSym.eq_one_iff' p
    (nat_residue_ne p a.natAbs ha0 hap)).mp (by rw [legendreSym.to_jacobiSym]; exact hj)
  by_cases ha : 0≤a
  · have he : (a:ZMod p)=(a.natAbs:ZMod p) := by
      exact_mod_cast ((Int.natCast_natAbs a).trans (abs_of_nonneg ha)).symm
    rw [he]
    exact hs
  · have he : (a:ZMod p)= -(a.natAbs:ZMod p) := by
      have hh : (a.natAbs:ℤ)= -a := by rw [Int.natCast_natAbs,abs_of_neg (by omega)]
      exact_mod_cast (show a= -(a.natAbs:ℤ) by omega)
    have hn : IsSquare (-1:ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    simpa only [he,neg_one_mul] using hn.mul hs

/-- A prime coprime to the smaller odd denominator has symbol±1. If its
class is a square, nonnegativity forces+1; no extra gcd is needed. -/
theorem square_congruence_symbol (q : ℕ) (hq0 : 0<q) (hqp : q<p)
    (b : ℤ) (hd : (q:ℤ)∣b^2-(p:ℤ)) : jacobiSym (p:ℤ) q=1 := by
  have he := jacobi_congr (p:ℤ) (b^2) q hd
  rw [jacobiSym.pow_left] at he
  rcases prime_symbol_cases p q hq0 hqp with h|h
  · exact h
  · have hb := sq_nonneg (jacobiSym b q)
    omega

lemma two_symbol (q : ℕ) (hq : Odd q) (hmod : q%8=1 ∨ q%8=7) : jacobiSym 2 q=1 := by
  rw [jacobiSym.at_two hq,ZMod.χ₈_nat_eq_if_mod_eight]
  have ho : q%2≠0 := by rcases hq with ⟨k,hk⟩; omega
  simp only [if_neg ho,if_pos hmod]

/-- The original identity2p=(a+b)²+(a−b)² gives the second required
symbol. The q≡±1 mod8 factor is retained explicitly. -/
theorem twice_square_congruence_symbol (q : ℕ) (hq0 : 0<q) (hqp : q<p)
    (hq : Odd q) (hmod : q%8=1 ∨ q%8=7)
    (b : ℤ) (hd : (q:ℤ)∣b^2-2*(p:ℤ)) : jacobiSym (p:ℤ) q=1 := by
  have he := jacobi_congr (2*(p:ℤ)) (b^2) q hd
  rw [jacobiSym.mul_left,two_symbol q hq hmod,one_mul,jacobiSym.pow_left] at he
  rcases prime_symbol_cases p q hq0 hqp with h|h
  · exact h
  · have hb := sq_nonneg (jacobiSym b q)
    omega

end SignedJacobiRay318
