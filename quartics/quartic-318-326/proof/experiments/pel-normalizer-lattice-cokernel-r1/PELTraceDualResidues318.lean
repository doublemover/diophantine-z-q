module
public import PELOrderTraceDiscriminant318
public section
noncomputable section
namespace PELTraceDualResidues318
set_option maxHeartbeats 1000000

@[expose] def numerator (a b c d : ℤ) : ℤ :=
  42*a^2+42*a*c-b^2+5*b*d-42*c^2-5*d^2

theorem residue_two : ∀ b d : ZMod 2,
    -b^2+5*b*d-5*d^2=0 → b=0 ∧ d=0 := by decide
theorem residue_three : ∀ b d : ZMod 3,
    -b^2+5*b*d-5*d^2=0 → b=0 ∧ d=0 := by decide
theorem residue_seven : ∀ b d : ZMod 7,
    -b^2+5*b*d-5*d^2=0 → b=0 ∧ d=0 := by decide
theorem residue_five : ∀ a b c : ZMod 5,
    42*a^2+42*a*c-b^2-42*c^2=0 → b=0 ∧ a-2*c=0 := by decide

/-- These are the exact local obstructions in the trace-dual norm. The prime
five condition couples the first and third coordinates; it is not replaced
by four unrelated coordinate divisibility assumptions. -/
theorem integral_norm_congruences (a b c d : ℤ)
    (h : (210:ℤ)∣numerator a b c d) :
    (210:ℤ)∣b ∧ (42:ℤ)∣d ∧ (5:ℤ)∣a-2*c := by
  have h2 : (2:ℤ)∣numerator a b c d := dvd_trans (by norm_num) h
  have h3 : (3:ℤ)∣numerator a b c d := dvd_trans (by norm_num) h
  have h5 : (5:ℤ)∣numerator a b c d := dvd_trans (by norm_num) h
  have h7 : (7:ℤ)∣numerator a b c d := dvd_trans (by norm_num) h
  have hz2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr h2
  have hz3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3
  have hz5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr h5
  have hz7 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr h7
  norm_num [numerator] at hz2 hz3 hz5 hz7
  obtain ⟨hb2,hd2⟩ := residue_two (b:ZMod 2) (d:ZMod 2) (by norm_num at hz2 ⊢; all_goals exact hz2)
  obtain ⟨hb3,hd3⟩ := residue_three (b:ZMod 3) (d:ZMod 3) (by norm_num at hz3 ⊢; all_goals exact hz3)
  obtain ⟨hb7,hd7⟩ := residue_seven (b:ZMod 7) (d:ZMod 7) (by norm_num at hz7 ⊢; all_goals exact hz7)
  obtain ⟨hb5,hac5⟩ := residue_five (a:ZMod 5) (b:ZMod 5) (c:ZMod 5)
    (by norm_num at hz5 ⊢; all_goals exact hz5)
  have b2 := (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hb2
  have b3 := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb3
  have b5 := (ZMod.intCast_zmod_eq_zero_iff_dvd b 5).mp hb5
  have b7 := (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mp hb7
  have d2 := (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).mp hd2
  have d3 := (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp hd3
  have d7 := (ZMod.intCast_zmod_eq_zero_iff_dvd d 7).mp hd7
  have ac5 : (5:ℤ)∣a-2*c := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    (by push_cast; exact hac5)
  exact ⟨by omega,by omega,ac5⟩
end PELTraceDualResidues318
