module
public import OddInfinityCanonicalCoefficients318
public import UnitDifferentTensorCancellation318
public section
noncomputable section
namespace OddInfinityIntegralCanonicalTensors318
open OddInfinityWholeModelMap318 OddInfinityCanonicalCoefficients318
open scoped TensorProduct
variable (V : Type*) [CommRing V] (pi : V) (u : Fin 4 → Vˣ) (a : Fin 4 → V)
local notation "C" => OddInfinitySmoothChart318.ModelRing V pi u a

/-- A literal element of the canonical tensor square of the produced
SMOOTH integral chart, not of a substitute rank-one lattice. -/
@[expose] def integralSection (k : C) :
    KaehlerDifferential V C ⊗[C] KaehlerDifferential V C :=
  k • (KaehlerDifferential.D V C (z V pi u a) ⊗ₜ[C]
    KaehlerDifferential.D V C (z V pi u a))
@[expose] def integral0 := integralSection V pi u a (coefficient0 V pi u a)
@[expose] def integral1 := integralSection V pi u a (coefficient1 V pi u a)

variable {B : Type*} [CommRing B] [Algebra V B] (f : C →ₐ[V] B)
  (h2 : IsUnit (2:V))
include h2 in
lemma differential_reciprocal :
    KaehlerDifferential.D V B (f (s V pi u a))=
      f (derivative V pi u a) • KaehlerDifferential.D V B (f (z V pi u a)) := by
  have h := congrArg (BaseChangingDifferentialTensor318.differential (S:=V) f)
    (D_reciprocal V pi u a h2)
  rw [BaseChangingDifferentialTensor318.differential_D,
    BaseChangingDifferentialTensor318.differential_smul,
    BaseChangingDifferentialTensor318.differential_D] at h
  exact h

lemma tensorMap_integral (k : C) :
    BaseChangingDifferentialTensor318.tensorMap (S:=V) f (integralSection V pi u a k)=
      f k • (KaehlerDifferential.D V B (f (z V pi u a)) ⊗ₜ[B]
        KaehlerDifferential.D V B (f (z V pi u a))) := by
  rw [integralSection,BaseChangingDifferentialTensor318.tensorMap_weighted,
    BaseChangingDifferentialTensor318.pureImage_D]

include h2 in
/-- Universal comparison with the true integral tensor section on ANY
coefficient extension where the actual different becomes a unit. -/
theorem realization (δ : Bˣ) (hδ : (δ:B)=f (different V pi u a))
    (k p : C) (h : k*(different V pi u a)^2=p*(derivative V pi u a)^2) :
    f p • (((↑δ⁻¹:B) • KaehlerDifferential.D V B (f (s V pi u a))) ⊗ₜ[B]
      ((↑δ⁻¹:B) • KaehlerDifferential.D V B (f (s V pi u a))))=
    BaseChangingDifferentialTensor318.tensorMap (S:=V) f (integralSection V pi u a k) := by
  rw [tensorMap_integral]
  simp only [differential_reciprocal V pi u a f h2,smul_smul]
  apply UnitDifferentTensorCancellation318.tensor
  rw [hδ,←map_pow,←map_mul,h,map_mul,map_pow]
end OddInfinityIntegralCanonicalTensors318
