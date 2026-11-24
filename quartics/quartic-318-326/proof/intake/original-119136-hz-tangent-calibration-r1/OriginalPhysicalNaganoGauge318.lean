module
public import OriginalPhysicalNaganoFourRoot318
public import OriginalPolarizedContactGauge318

/-! Bind the original named coarse radicals at T=119136 to the exact contact
scalar in the calibrated theta gauge. This is a native arithmetic attachment,
not a producer of a represented PEL model or its Kodaira–Spencer calibration. -/

public section
namespace OriginalPhysicalNaganoGauge318

open OriginalPolarizedContactGauge318 (f g n p theta_scaled_read)
open OriginalPhysicalNaganoJet318 (nn dd)
open OriginalPhysicalNaganoReadback318 (h nonzero_dd)
open OriginalMarkedIntPolynomialCertificate318 (horner)

variable {K : Type*} [Field K]

private theorem original_n (z : K) : h z nn = n z := by
  simp only [h, nn, horner, n, Int.cast_ofNat, Int.cast_zero]
  ring

private theorem original_f (z : K) : h z dd = f z := by
  simp only [h, dd, horner, f, Int.cast_neg, Int.cast_ofNat]
  ring

variable [CharZero K]

/-- The main height scalar c is an exact rational number in the scaled theta
frame, with the true T inherited from the original Hilbert/radical receiver.
All four signed coarse choices use the same scalar. -/
theorem from_original (r₀ r₁ r₃ : K)
    (h₀ : r₀^2 = -14*119136) (h₁ : r₁^2 = -6*(119136-32))
    (h₃ : r₃^2 = -21*(119136+343)) :
    let z := (8*r₃/r₀-15)/(49*r₁/r₀-30)
    n z / f z = 119136 ∧
    (p (119136 : K) *
      ((1+z^2)^2 * ((-12600) * f z^3 / (g z * OriginalPolarizedContactGauge318.h z^2))))⁻¹
      = 1 / 28145880000 := by
  dsimp only
  let z : K := (8*r₃/r₀-15)/(49*r₁/r₀-30)
  have ht0 := (OriginalPhysicalNaganoFourRoot318.from_original r₀ r₁ r₃ h₀ h₁ h₃).1
  have ht : n z / f z = 119136 := by
    change h z nn / h z dd = 119136 at ht0
    simpa only [original_n, original_f] using ht0
  have hz := OriginalPhysicalNaganoFourRoot318.root_from_original r₀ r₁ r₃ h₀ h₁ h₃
  have hf : f z ≠ 0 := by
    simpa only [original_f] using nonzero_dd z hz
  have hp : p (n z / f z) ≠ 0 := by
    rw [ht]
    norm_num [p]
  have hc := theta_scaled_read z hf hp
  rw [ht] at hc
  exact ⟨ht, by simpa only [show (236250 : K) * 119136 = 28145880000 by norm_num] using hc⟩

end OriginalPhysicalNaganoGauge318

#print axioms OriginalPhysicalNaganoGauge318.from_original
