module
public import ActualTwoDescentInfinityNativeDVR318
public section
noncomputable section
namespace ActualTwoDescentInfinityNormalizedOrders318
open ActualTwoDescentInfinityLocalParameter318 ActualTwoDescentInfinityNativeDVR318
open ActualTwoDescentInfinityRootUnitFactors318 IsDiscreteValuationRing
variable {K : Type*} [Field K] [CharZero K]

/-- Native DVR normalization is proved on the original coordinate u. -/
theorem actual_infinity_order_u (n : K) : addVal (InfinityLocalRing n) (localU n)=1 :=
  addVal_uniformizer (actual_infinity_u_irreducible n)

/-- Exact order THREE of v at the actual original point at infinity. -/
theorem actual_infinity_order_v (n : K) : addVal (InfinityLocalRing n) (localV n)=3 := by
  obtain ⟨e,he⟩ := actual_local_v_unit_cube n
  exact addVal_def _ e (actual_infinity_u_irreducible n) 3 he

/-- Exact order ONE of every affine root numerator u-a*v. No generic
noncancellation or unproved unit hypothesis remains. -/
theorem actual_infinity_order_root_numerator (n a : K) :
    addVal (InfinityLocalRing n) (localU n-localCoefficient n a*localV n)=1 := by
  obtain ⟨d,hd⟩ := actual_local_root_numerator n a
  apply addVal_def _ d (actual_infinity_u_irreducible n) 1
  rw [hd]
  ring

end ActualTwoDescentInfinityNormalizedOrders318
