module
public import OddInfinityGenericCanonical318
public import NormalizedWholeTensorSections318
public section
noncomputable section
namespace OddInfinityGlobalCanonicalSections318
open AlgebraicGeometry
open scoped TensorProduct
variable (V : Type*) [CommRing V] (pi : V) (u : Fin 4 → Vˣ) (d a : Fin 4 → V)
  (ha : a 0=0) (hd : ∀ i,d i=(u i:V)*pi)
local notation "L" => NormalizedWholeDualitySheaf318.line V d a
local notation "T" => IntrinsicTensorSheaf318.tensor L L
/-- Actual restriction of an arbitrary GLOBAL tensor section, followed by
its whole finite-dual realization on the same different-unit open. -/
@[expose] def globalImage (s : Γ(T,⊤)) :=
  OddInfinityGenericCanonical318.realization V pi u d a ha hd
    (NormalizedWholeTensorSections318.infinityTensor V d a s)

variable (h2 : IsUnit (2:V))
include h2 in
theorem global0_integral : globalImage V pi u d a ha hd
    (NormalizedWholeIntrinsicTensor318.section0 V d a)=
      BaseChangingDifferentialTensor318.tensorMap (S:=V)
        (OddInfinityGenericCanonical318.baseMap V pi u a)
        (OddInfinityIntegralCanonicalTensors318.integral0 V pi u a) := by
  rw [globalImage,NormalizedWholeTensorSections318.section0_infinity]
  exact OddInfinityGenericCanonical318.section0_integral V pi u d a ha hd h2

include h2 in
theorem global1_integral : globalImage V pi u d a ha hd
    (NormalizedWholeIntrinsicTensor318.section1 V d a)=
      BaseChangingDifferentialTensor318.tensorMap (S:=V)
        (OddInfinityGenericCanonical318.baseMap V pi u a)
        (OddInfinityIntegralCanonicalTensors318.integral1 V pi u a) := by
  rw [globalImage,NormalizedWholeTensorSections318.section1_infinity]
  exact OddInfinityGenericCanonical318.section1_integral V pi u d a ha hd h2
end OddInfinityGlobalCanonicalSections318
