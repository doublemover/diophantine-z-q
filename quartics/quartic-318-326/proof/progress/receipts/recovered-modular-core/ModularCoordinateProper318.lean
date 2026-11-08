module
public import ModularArithmeticCoordinates318
public import Mathlib.Topology.LocalAtTarget
public section
noncomputable section
open Filter Set
open scoped Topology
namespace ModularCoordinateProper318
open ThreeArithmeticQuotient318 ModularArithmeticCoordinates318
set_option maxHeartbeats 0

abbrev JOpen := {z : ℂ // z≠0 ∧ z≠1728}
@[expose] def sourceJ (q : Source) : JOpen := ⟨QuotientJ318.jMap 3 q.val,q.property⟩

lemma sourceJ_continuous : Continuous sourceJ :=
  ((ActualJAllLevels318.continuous_j 3).comp continuous_subtype_val).subtype_mk _

/-- Genuine j restricted to its actual nonexceptional inverse image is proper. -/
theorem sourceJ_proper : IsProperMap sourceJ :=
  (ActualJAllLevels318.proper 3).restrictPreimage {z : ℂ | z≠0 ∧ z≠1728}

@[expose] def openCoordinates (q : Source) : JOpen × ℂ := (sourceJ q,sourceX q)

lemma openCoordinates_continuous : Continuous openCoordinates :=
  sourceJ_continuous.prodMk sourceX_continuous

/-- The two actual arithmetic coordinates together give a topologically proper map. -/
theorem openCoordinates_proper : IsProperMap openCoordinates :=
  isProperMap_of_comp_of_t2 openCoordinates_continuous continuous_fst sourceJ_proper

lemma finite_fiber (p : JOpen × ℂ) : (openCoordinates ⁻¹' {p}).Finite := by
  have hj := ActualJAllLevels318.finite_fiber 3 p.1.val
  have hf := hj.preimage (f := fun q : Source => q.val) Subtype.val_injective.injOn
  apply hf.subset
  intro q hq
  change openCoordinates q=p at hq
  change QuotientJ318.jMap 3 q.val=p.1.val
  exact congrArg (fun r : JOpen × ℂ => r.1.val) hq

end ModularCoordinateProper318
