module
public import ScalarTwoThreePreparation318
public section
noncomputable section
namespace ScalarPreparedCongruence318
open ScalarTwoThreePreparation318 ScalarForwardWitness318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- This label is fixed before the real region, contact parameter and prime
pattern. Its translated index has depth at least21 at both2 and3. The free positive multiplier remains available for other prime conditions. -/
@[expose] def scalarLabel (d : ℕ) : ℤ := 1+(6^21*d:ℕ)

lemma label_domains (d : ℕ) (hd : d≠0) :
    scalarLabel d≠0 ∧ scalarLabel d≠1 ∧ Even (scalarLabel d-1) := by
  have hpos : (0:ℤ)<(6^21*d:ℕ) := by positivity
  have he : scalarLabel d-1=((6^21*d:ℕ):ℤ) := by simp [scalarLabel]
  refine ⟨by unfold scalarLabel; omega,by unfold scalarLabel; omega,?_⟩
  rw [he]
  have hdiv : (2:ℕ)∣6^21*d :=
    (by norm_num : (2:ℕ)∣6^21).mul_right d
  exact_mod_cast even_iff_two_dvd.mpr hdiv

lemma label_depths (d : ℕ) (hd : d≠0) :
    21≤padicValInt 2 (scalarLabel d-1) ∧ 21≤padicValInt 3 (scalarLabel d-1) := by
  have h₂ : padicValNat 2 6=1 := by
    rw [show (6:ℕ)=2*3 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,padicValNat_primes (by decide : 2≠3)]
    norm_num
  have h₃ : padicValNat 3 6=1 := by
    rw [show (6:ℕ)=3*2 by norm_num,padicValNat.mul (by norm_num) (by norm_num),
      padicValNat_self,padicValNat_primes (by decide : 3≠2)]
    norm_num
  have he : scalarLabel d-1=((6^21*d:ℕ):ℤ) := by simp [scalarLabel]
  rw [he,padicValInt.of_nat,padicValInt.of_nat,
    padicValNat.mul (by positivity : (6:ℕ)^21≠0) hd,
    padicValNat.mul (by positivity : (6:ℕ)^21≠0) hd,
    padicValNat.pow,padicValNat.pow,h₂,h₃]
  omega

/-- A concrete initial local congruence, compatible with h divisible64,
preserves the precise common-index depths needed by the fixed scalar label. -/
lemma common_depths (h : ℕ) (hc : Nat.ModEq 384 h 64) :
    (h:ℤ)≠0 ∧ Even (h:ℤ) ∧ padicValInt 2 (h:ℤ)=6 ∧ padicValInt 3 (h:ℤ)=0 := by
  have h128 : h%128=64 := by
    simpa only [Nat.ModEq,show 64%128=64 by decide] using hc.of_dvd (by norm_num : 128∣384)
  have h3 : h%3=1 := by
    simpa only [Nat.ModEq,show 64%3=1 by decide] using hc.of_dvd (by norm_num : 3∣384)
  have hn : h≠0 := by omega
  have h64 : 64∣h := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have hnot128 : ¬128∣h := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have htwo : 6≤padicValNat 2 h :=
    (padicValNat_dvd_iff_le hn).mp (by simpa using h64)
  have htwo' : ¬7≤padicValNat 2 h := by
    intro he
    exact hnot128 (by simpa using (padicValNat_dvd_iff_le hn).mpr he)
  have heven : Even h := even_iff_two_dvd.mpr ((by norm_num : 2∣64).trans h64)
  refine ⟨by exact_mod_cast hn,by exact_mod_cast heven,?_,?_⟩
  · rw [padicValInt.of_nat]
    omega
  · rw [padicValInt.of_nat]
    exact padicValNat.eq_zero_of_not_dvd (by rw [Nat.dvd_iff_mod_eq_zero]; omega)

/-- Both actual packed local units are now produced from a fixed label and
one explicit common-index congruence, with no valuation hypotheses. -/
theorem actual_two_three_units (a : ℤ) (labels : Fin 4 → ℤ)
    (d : ℕ) (hd : d≠0) (hl : labels 1=scalarLabel d) (h : ℕ) (hc : Nat.ModEq 384 h 64) :
    padicValRat 2 (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 ∧
    padicValRat 3 (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 := by
  obtain ⟨hh,heven,h₂,h₃⟩ := common_depths h hc
  obtain ⟨hn,hn1,hneven⟩ := label_domains d hd
  obtain ⟨n₂,n₃⟩ := label_depths d hd
  rw [←hl] at hn hn1 hneven n₂ n₃
  exact ⟨unit_two a labels (h:ℤ) hh hn hn1 (by omega),
    unit_three a labels (h:ℤ) hh heven hn hn1 hneven (by omega)⟩

/-- The original mixed CRT continuity congruence retains the concrete local
preparation when the modulus and initial residue were fixed accordingly. -/
theorem continuity_preserves_units (a : ℤ) (labels : Fin 4 → ℤ)
    (d : ℕ) (hd : d≠0) (hl : labels 1=scalarLabel d) (h L h₀ : ℕ)
    (hL : 384∣L) (hh₀ : Nat.ModEq 384 h₀ 64) (hh : Nat.ModEq L h h₀) :
    padicValRat 2 (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 ∧
    padicValRat 3 (W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 :=
  actual_two_three_units a labels d hd hl h ((hh.of_dvd hL).trans hh₀)

end ScalarPreparedCongruence318
