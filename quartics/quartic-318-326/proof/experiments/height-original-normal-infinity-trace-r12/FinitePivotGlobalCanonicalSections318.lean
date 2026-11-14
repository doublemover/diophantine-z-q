module
public import FinitePivotGenericCanonical318
public import NormalizedWholeTensorSections318
public section
noncomputable section
namespace FinitePivotGlobalCanonicalSections318
open AlgebraicGeometry
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (rho : V) (u : Vˣ) (d a : Fin 4 → V) (i : Fin 4) (hd : d i=(u:V)*rho)
local notation "L" => NormalizedWholeDualitySheaf318.line V d a
local notation "T" => IntrinsicTensorSheaf318.tensor L L
/-- Actual restriction of an arbitrary GLOBAL tensor section, followed by
its whole finite-dual realization on the same different-unit open. -/
@[expose] def globalImage (s : Γ(T,⊤)) :=
  FinitePivotGenericCanonical318.realization V rho u d a i hd
    (NormalizedWholeTensorSections318.finiteTensor V d a s)

variable (h2 : IsUnit (2:V))
include h2 in
theorem global0_integral : globalImage V rho u d a i hd
    (NormalizedWholeIntrinsicTensor318.section0 V d a)=
      BaseChangingDifferentialTensor318.tensorMap (S:=V)
        (FinitePivotGenericCanonical318.baseMap V rho u d a i)
        (FinitePivotIntegralCanonicalTensors318.integral0 V rho u d a i) := by
  rw [globalImage,NormalizedWholeTensorSections318.section0_finite]
  exact FinitePivotGenericCanonical318.section0_integral V rho u d a i hd h2

include h2 in
theorem global1_integral : globalImage V rho u d a i hd
    (NormalizedWholeIntrinsicTensor318.section1 V d a)=
      BaseChangingDifferentialTensor318.tensorMap (S:=V)
        (FinitePivotGenericCanonical318.baseMap V rho u d a i)
        (FinitePivotIntegralCanonicalTensors318.integral1 V rho u d a i) := by
  rw [globalImage,NormalizedWholeTensorSections318.section1_finite]
  exact FinitePivotGenericCanonical318.section1_integral V rho u d a i hd h2
end FinitePivotGlobalCanonicalSections318
