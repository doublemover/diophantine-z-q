module
public import ConcreteOriginalSixteenDenominator318
public section
noncomputable section
namespace AdditionalSixteenDenominators318
open ConcreteOriginalSixteenDenominator318 SelectedEntryDenominatorDivisibility318
open SelectedGlobalCoordinateDenominators318 ConcreteG8Domain
lemma residue_95441 : multipleDenominator 16%95441=93979 := by
  unfold multipleDenominator pointDenominator
  rw [coordinate]
  norm_num [denominator,x16,pair]
lemma nondiv_95441 : ¬95441∣multipleDenominator 16 := by
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [residue_95441] at hz
  norm_num at hz
lemma residue_387089 : multipleDenominator 16%387089=331056 := by
  unfold multipleDenominator pointDenominator
  rw [coordinate]
  norm_num [denominator,x16,pair]
lemma nondiv_387089 : ¬387089∣multipleDenominator 16 := by
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [residue_387089] at hz
  norm_num at hz
lemma residue_1473041 : multipleDenominator 16%1473041=861433 := by
  unfold multipleDenominator pointDenominator
  rw [coordinate]
  norm_num [denominator,x16,pair]
lemma nondiv_1473041 : ¬1473041∣multipleDenominator 16 := by
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [residue_1473041] at hz
  norm_num at hz
end AdditionalSixteenDenominators318
