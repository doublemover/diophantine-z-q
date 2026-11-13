module
public import PELOriginalCM210BoundedMaximalIdeals318
public section
noncomputable section
namespace PELOriginalCM210BoundedIdealFactors318
open PELOriginalCM210NativeIntegerOrder318
lemma norms_of_product (I J:Ideal O) (hI:I≠⊥) (hJ:J≠⊥)
    (h:Ideal.absNorm (I*J)≤18) :
    Ideal.absNorm I≤18 ∧ Ideal.absNorm J≤18 := by
  have hi : 0<Ideal.absNorm I :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hI)
  have hj : 0<Ideal.absNorm J :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hJ)
  rw [map_mul] at h
  constructor
  · exact le_trans (by simpa only [mul_one] using
      Nat.mul_le_mul_left (Ideal.absNorm I) hj) h
  · exact le_trans (by simpa only [one_mul] using
      Nat.mul_le_mul_right (Ideal.absNorm J) hi) h
end PELOriginalCM210BoundedIdealFactors318
