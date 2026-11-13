module
public import SignedJacobiRay318
public section
noncomputable section
namespace GaussianRayQuadratic318
open SignedJacobiRay318
set_option maxHeartbeats 1000000

@[expose] def Ray (p : ℕ) (a b : ℤ) : Prop :=
  (p:ℤ)=a^2+b^2 ∧ a%16=9 ∧ b%16=0

lemma abs_dvd (a : ℤ) : (a.natAbs:ℤ)∣a := by
  by_cases ha : 0≤a
  · refine ⟨1,?_⟩
    rw [mul_one,Int.natCast_natAbs,abs_of_nonneg ha]
  · refine ⟨-1,?_⟩
    rw [Int.natCast_natAbs,abs_of_neg (by omega)]
    ring

lemma abs_mod_eight (a : ℤ) (ha : a%8=1) : a.natAbs%8=1 ∨ a.natAbs%8=7 := by
  have he : (a.natAbs:ℤ)=a ∨ (a.natAbs:ℤ)= -a := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 a with hh|hh
    · exact Or.inl (abs_of_nonneg hh)
    · exact Or.inr (abs_of_nonpos hh)
  have hh : (a.natAbs:ℤ)%8=1 ∨ (a.natAbs:ℤ)%8=7 := by rcases he with he|he <;> omega
  exact_mod_cast hh

lemma abs_odd (a : ℤ) (ha : a%8=1) : Odd a.natAbs := by
  have hm := abs_mod_eight a ha
  refine ⟨a.natAbs/2,?_⟩
  omega

variable (p : ℕ) [Fact p.Prime]
lemma prime_mod (a b : ℤ) (h : Ray p a b) : p%16=1 := by
  have he : (p:ℤ)%16=1 := by
    rw [h.1]
    norm_num [Int.add_emod,Int.pow_emod,h.2.1,h.2.2]
  exact_mod_cast he

/-- Both signed numerators have positive absolute value below p, so all
Jacobi reciprocity and unit conditions are derived from the actual norm/ray. -/
theorem bounds (a b : ℤ) (h : Ray p a b) :
    0<a.natAbs ∧ a.natAbs<p ∧ 0<(a+b).natAbs ∧ (a+b).natAbs<p := by
  have hm := prime_mod p a b h
  have hpNat : 2<p := by have hh := (Fact.out : p.Prime).two_le; omega
  have hp : (2:ℤ)<p := by exact_mod_cast hpNat
  have ha0 : a≠0 := by intro he; have hh := h.2.1; rw [he] at hh; norm_num at hh
  have hsum : (a+b)%8=1 := by have ha := h.2.1; have hb := h.2.2; omega
  have hs0 : a+b≠0 := by intro he; rw [he] at hsum; norm_num at hsum
  have ha2 : (a.natAbs:ℤ)^2=a^2 := by rw [Int.natCast_natAbs,sq_abs]
  have hs2 : ((a+b).natAbs:ℤ)^2≤2*(p:ℤ) := by
    rw [Int.natCast_natAbs,sq_abs]
    nlinarith [h.1,sq_nonneg (a-b)]
  have hab : (a.natAbs:ℤ)<p := by nlinarith [h.1,sq_nonneg b,Int.natCast_nonneg a.natAbs]
  have hsb : ((a+b).natAbs:ℤ)<p := by nlinarith [Int.natCast_nonneg (a+b).natAbs]
  exact ⟨Int.natAbs_pos.mpr ha0,by exact_mod_cast hab,
    Int.natAbs_pos.mpr hs0,by exact_mod_cast hsb⟩

/-- Ordinary Jacobi reciprocity produces both actual quadratic residues;
all sign, denominator, coprimality and q=1 cases are retained. -/
theorem two_squares (a b : ℤ) (h : Ray p a b) :
    IsSquare (a:ZMod p) ∧ IsSquare ((a+b:ℤ):ZMod p) := by
  obtain ⟨ha0,hap,hs0,hsp⟩ := bounds p a b h
  have hp4 : p%4=1 := by have hm := prime_mod p a b h; omega
  have ha8 : a%8=1 := by have ha := h.2.1; omega
  have hs8 : (a+b)%8=1 := by have ha := h.2.1; have hb := h.2.2; omega
  have hdA : (a.natAbs:ℤ)∣b^2-(p:ℤ) := by
    obtain ⟨k,hk⟩ := abs_dvd a
    refine ⟨-(a.natAbs:ℤ)*k^2,?_⟩
    have hs := congrArg (fun z : ℤ => z^2) hk
    rw [h.1]
    linear_combination -hs
  have hdS : ((a+b).natAbs:ℤ)∣(a-b)^2-2*(p:ℤ) := by
    obtain ⟨k,hk⟩ := abs_dvd (a+b)
    refine ⟨-((a+b).natAbs:ℤ)*k^2,?_⟩
    have hs := congrArg (fun z : ℤ => z^2) hk
    rw [h.1]
    linear_combination -hs
  exact ⟨square_from_reciprocity p hp4 a ha0 hap (abs_odd a ha8)
      (square_congruence_symbol p a.natAbs ha0 hap b hdA),
    square_from_reciprocity p hp4 (a+b) hs0 hsp (abs_odd (a+b) hs8)
      (twice_square_congruence_symbol p (a+b).natAbs hs0 hsp
        (abs_odd (a+b) hs8) (abs_mod_eight (a+b) hs8) (a-b) hdS)⟩

theorem actual_roots (a b : ℤ) (h : Ray p a b) :
    ∃ z t : ZMod p, z^8= -1 ∧ t^4=2 := by
  obtain ⟨ha0,hap,hs0,hsp⟩ := bounds p a b h
  obtain ⟨ha,hs⟩ := two_squares p a b h
  have hnorm : (a:ZMod p)^2+(b:ZMod p)^2=0 := by
    have he := congrArg (fun n : ℤ => (n:ZMod p)) h.1
    simpa only [Int.cast_add,Int.cast_pow,Int.cast_natCast,ZMod.natCast_self] using he.symm
  have hpow := FiniteRayRootAlgebra318.quartic_euler p (prime_mod p a b h)
    (a:ZMod p) (b:ZMod p) (int_residue_ne p a ha0 hap)
    (by simpa only [Int.cast_add] using int_residue_ne p (a+b) hs0 hsp) hnorm ha
    (by simpa only [Int.cast_add] using hs)
  obtain ⟨z,hz⟩ := FiniteRayRootAlgebra318.eighth_root_neg_one p (prime_mod p a b h)
  obtain ⟨t,ht⟩ := FiniteRayRootAlgebra318.fourth_root_two p (prime_mod p a b h) hpow
  exact ⟨z,t,hz,ht⟩

end GaussianRayQuadratic318
