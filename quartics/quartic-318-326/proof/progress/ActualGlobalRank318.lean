module
public import ActualRankOne318
public import ActualCanonicalHeight318
public section
namespace ActualGlobalRank318
open ConcreteG8Domain LocalGenerator318

/-- The actual curve's torsion subgroup is killed by two, using the
constructed canonical height and checked finite small-height certificate. -/
theorem torsion_killed_by_two (Q:E.Point) (hQ:IsOfFinAddOrder Q) : Q+Q=0 :=
  GlobalTorsionOddIndex318.torsion_is_two_torsion ActualCanonicalHeight318.canonical_data Q hQ

/-- The exact global rank-one and odd-index assertion, with no arithmetic,
height, finite-generation, torsion, or rank premises left. -/
theorem odd_rank_one_data : GlobalSaturationLogic318.OddRankOneData :=
  ActualRankOne318.odd_rank_one torsion_killed_by_two

theorem free_rank_eq_one : Module.finrank ℤ ActualFreePart318.FreePart=1 :=
  ActualRankOne318.free_rank_one torsion_killed_by_two

end ActualGlobalRank318
#print axioms ActualGlobalRank318.odd_rank_one_data
#print axioms ActualGlobalRank318.free_rank_eq_one
