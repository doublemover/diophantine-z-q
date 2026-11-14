module
public import ActualTwoDescentOriginalRootNativeDVR318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootNormalizedOrders318
open ActualTwoDescentOriginalRootLocalParameter318 ActualTwoDescentOriginalRootNativeDVR318
open IsDiscreteValuationRing
variable {K : Type*} [Field K] [CharZero K]

lemma actual_root_order_y (n : K) (i : Fin 3) [Fact (n≠0)] :
    addVal (RootLocalRing n i) (rootLocalY n i)=1 :=
  addVal_uniformizer (actual_root_y_irreducible n i)
/-- Exact order TWO of the earlier affine root function at its own point. -/
theorem actual_root_order_f (n : K) (i : Fin 3) [Fact (n≠0)] :
    addVal (RootLocalRing n i) (rootLocalF n i)=2 := by
  obtain ⟨e,he⟩ := actual_root_local_unit_square n Fact.out i
  exact addVal_def _ e (actual_root_y_irreducible n i) 2 he
lemma actual_root_order_cofactor (n : K) (i : Fin 3) [Fact (n≠0)] :
    addVal (RootLocalRing n i) (rootLocalQ n i)=0 :=
  addVal_eq_zero_iff.mpr (actual_root_local_cofactor_unit n Fact.out i)
end ActualTwoDescentOriginalRootNormalizedOrders318
