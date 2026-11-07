module
public import ConsumedContactHeight318
public section
namespace ContactMapEndpoints318
open ContactRadical318 ContactHeight318 NumberField
noncomputable section
set_option maxHeartbeats 0

/-- The degenerate detector actually has empty good odd-contact support. -/
theorem detector_one_primes : detectorPrimes (1:ℚ)=∅ := by decide +kernel

theorem detector_one_radical : detectorRadical (1:ℚ)=1 := by
  change (∏p∈detectorPrimes (1:ℚ),p)=1
  rw [detector_one_primes]
  simp

/-- The primitive tuple in the contact theorem is the actual fractional-linear
image phi(t)=2+1/t; its projective height is not a substitute height. -/
theorem detector_phi_height (t:ℚ) (ht:t≠0) :
    pointHeight (2*t.num+t.den) t.num=absLogHeight₁ (2+1/t) := by
  have hn:t.num≠0:=Rat.num_ne_zero.mpr ht
  have h0:(t.num:ℚ)≠0:=by exact_mod_cast hn
  have hv : (t.num:ℚ) • (![2+1/t,1]:Fin 2→ℚ)=
      ![((2*t.num+t.den:ℤ):ℚ),(t.num:ℚ)] := by
    ext i
    fin_cases i
    · simp only [Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero]
      push_cast
      field_simp [ht]
      nlinarith [t.den_mul_eq_num]
    · simp
  rw [DetectorHeightTransfer318.rational_height_eq,Height.logHeight₁_eq_logHeight]
  change Height.logHeight (![((2*t.num+t.den:ℤ):ℚ),(t.num:ℚ)] : Fin 2→ℚ)=_
  rw [←hv,Height.logHeight_smul_eq_logHeight _ h0]

end
end ContactMapEndpoints318
#print axioms ContactMapEndpoints318.detector_one_primes
#print axioms ContactMapEndpoints318.detector_phi_height
