module
public import FinitePivotCanonicalCoefficients318
public import UnitDifferentTensorCancellation318
public section
noncomputable section
namespace FinitePivotIntegralCanonicalTensors318
open FinitePivotCanonicalSource318 FinitePivotCanonicalCoefficients318
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (rho : V) (u : Vˣ) (d a : Fin 4 → V) (i : Fin 4)
local notation "C" => FinitePivotCanonicalSource318.Chart V rho u d a i

/-- A literal element of the canonical tensor square of the produced
SMOOTH integral chart, not of a substitute rank-one lattice. -/
@[expose] def integralSection (k : C) :
    KaehlerDifferential V C ⊗[C] KaehlerDifferential V C :=
  k • (KaehlerDifferential.D V C (z V rho u d a i) ⊗ₜ[C]
    KaehlerDifferential.D V C (z V rho u d a i))
@[expose] def integral0 := integralSection V rho u d a i (coefficient0 V rho u d a i)
@[expose] def integral1 := integralSection V rho u d a i (coefficient1 V rho u d a i)

variable {B : Type*} [CommRing B] [Algebra V B] (f : C →ₐ[V] B)
  (h2 : IsUnit (2:V))
include h2 in
lemma differential_contact :
    KaehlerDifferential.D V B (f (t V rho u d a i))=
      f (derivative V rho u d a i) • KaehlerDifferential.D V B (f (z V rho u d a i)) := by
  have h := congrArg (BaseChangingDifferentialTensor318.differential (S:=V) f)
    (D_contact V rho u d a i h2)
  rw [BaseChangingDifferentialTensor318.differential_D,
    BaseChangingDifferentialTensor318.differential_smul,
    BaseChangingDifferentialTensor318.differential_D] at h
  exact h

lemma tensorMap_integral (k : C) :
    BaseChangingDifferentialTensor318.tensorMap (S:=V) f (integralSection V rho u d a i k)=
      f k • (KaehlerDifferential.D V B (f (z V rho u d a i)) ⊗ₜ[B]
        KaehlerDifferential.D V B (f (z V rho u d a i))) := by
  rw [integralSection,BaseChangingDifferentialTensor318.tensorMap_weighted,
    BaseChangingDifferentialTensor318.pureImage_D]

include h2 in
/-- Universal comparison with the true integral tensor section on ANY
coefficient extension where the actual different becomes a unit. -/
theorem realization (δ : Bˣ) (hδ : (δ:B)=f (different V rho u d a i))
    (k p : C) (h : k*(different V rho u d a i)^2=p*(derivative V rho u d a i)^2) :
    f p • (((↑δ⁻¹:B) • KaehlerDifferential.D V B (f (t V rho u d a i))) ⊗ₜ[B]
      ((↑δ⁻¹:B) • KaehlerDifferential.D V B (f (t V rho u d a i))))=
    BaseChangingDifferentialTensor318.tensorMap (S:=V) f (integralSection V rho u d a i k) := by
  rw [tensorMap_integral]
  simp only [differential_contact V rho u d a i f h2,smul_smul]
  apply UnitDifferentTensorCancellation318.tensor
  rw [hδ,←map_pow,←map_mul,h,map_mul,map_pow]
end FinitePivotIntegralCanonicalTensors318
