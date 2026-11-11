module
public import BaseChangingDifferentialTensor318
public section
noncomputable section
namespace UnitDifferentTensorCancellation318
open scoped TensorProduct
variable {B : Type*} [CommRing B]

lemma coefficient (k p d : B) (δ : Bˣ) (h : k*(δ:B)^2=p*d^2) :
    p*((↑δ⁻¹:B)*d)^2=k := by
  calc
    _ = (p*d^2)*(↑δ⁻¹:B)^2 := by ring
    _ = (k*(δ:B)^2)*(↑δ⁻¹:B)^2 := by rw [←h]
    _ = k*((δ:B)*(↑δ⁻¹:B))^2 := by ring
    _ = k := by rw [Units.mul_inv,one_pow,mul_one]

/-- Cancellation in the ENTIRE balanced tensor square. Only the specified
actual different is inverted, after passing to its genuine unit open. -/
theorem tensor {M : Type*} [AddCommGroup M] [Module B M]
    (k p d : B) (δ : Bˣ) (h : k*(δ:B)^2=p*d^2) (ω : M) :
    p • (((↑δ⁻¹:B)*d) • ω ⊗ₜ[B] ((↑δ⁻¹:B)*d) • ω)=k • (ω ⊗ₜ[B] ω) := by
  rw [TensorProduct.smul_tmul',TensorProduct.tmul_smul,smul_smul,smul_smul]
  congr 1
  simpa only [pow_two,mul_assoc] using coefficient k p d δ h
end UnitDifferentTensorCancellation318
