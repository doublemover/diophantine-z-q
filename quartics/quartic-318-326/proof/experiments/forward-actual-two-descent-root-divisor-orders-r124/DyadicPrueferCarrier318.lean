module
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Topology.Instances.AddCircle.Defs
public section
namespace ActualTwoDescentDyadicPrueferModel318

/-- The standard dyadic Prüfer group, literally the2-primary subgroup of Q/Z. -/
abbrev PrueferTwo := CommGroup.primaryComponent (Multiplicative (AddCircle (1 : ℚ))) 2

end ActualTwoDescentDyadicPrueferModel318
