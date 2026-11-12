module
public import ActualTwoDescentCirclePrimaryPruefer318
public section
noncomputable section
namespace ActualTwoDescentDiscreteSelmerDual318
set_option maxHeartbeats 16000000
open ActualTwoDescentActualPrimarySelmer318

/-- A distinct type synonym fixes the ACTUAL Selmer group with its discrete
topology, without overwriting any topology on a cohomology presentation. -/
def DiscreteSelmer (n : ℚ) (hn : n ≠ 0) := Multiplicative (actualPrimarySelmer n hn)
instance (n : ℚ) (hn : n ≠ 0) : CommGroup (DiscreteSelmer n hn) :=
  inferInstanceAs (CommGroup (Multiplicative (actualPrimarySelmer n hn)))
instance (n : ℚ) (hn : n ≠ 0) : TopologicalSpace (DiscreteSelmer n hn) := ⊥
instance (n : ℚ) (hn : n ≠ 0) : DiscreteTopology (DiscreteSelmer n hn) := ⟨rfl⟩
instance (n : ℚ) (hn : n ≠ 0) : IsTopologicalGroup (DiscreteSelmer n hn) := inferInstance

abbrev ActualPontryagin (n : ℚ) (hn : n ≠ 0) := PontryaginDual (DiscreteSelmer n hn)

lemma actual_pontryagin_compact (n : ℚ) (hn : n ≠ 0) : CompactSpace (ActualPontryagin n hn) := inferInstance
lemma actual_pontryagin_hausdorff (n : ℚ) (hn : n ≠ 0) : T2Space (ActualPontryagin n hn) := inferInstance

end ActualTwoDescentDiscreteSelmerDual318
