module
public import IntegralGluedChartGeometry318
public section
noncomputable section
namespace IntegralGluedTensorSections318
open AlgebraicGeometry CategoryTheory Opposite
open IntegralGluedModel318 IntegralGluedChartGeometry318
open IntrinsicTensorChartSections318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def tensor : (scheme R c).Modules :=
  IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega (structureMap R c))
    (FamilyIntrinsicDifferentials318.omega (structureMap R c))
@[expose] def branchQ0 : Γ(tensor R c,branchChart R c ''ᵁ ⊤) :=
  weightedSquare (branchChart R c) (structureMap R c) (branch_over_base R c)
    ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
      IntegralBranchBicanonical318.coefficient0 R c 0)
    (KaehlerDifferential.D R (IntegralBranchCoordinates318.B R c 0)
      (IntegralBranchCoordinates318.sourceCoordinate R c 0))
@[expose] def branchQ1 : Γ(tensor R c,branchChart R c ''ᵁ ⊤) :=
  weightedSquare (branchChart R c) (structureMap R c) (branch_over_base R c)
    ((VerticalSection318.J : IntegralBranchCoordinates318.B R c 0)^2 *
      IntegralBranchBicanonical318.coefficient1 R c 0)
    (KaehlerDifferential.D R (IntegralBranchCoordinates318.B R c 0)
      (IntegralBranchCoordinates318.sourceCoordinate R c 0))
@[expose] def infinityQ0 : Γ(tensor R c,infinityChart R c ''ᵁ ⊤) :=
  weightedSquare (infinityChart R c) (structureMap R c) (infinityChart_structure R c)
    ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
      IntegralInfinityCoefficients318.coefficient0 R c)
    (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c)
      (IntegralInfinityChart318.coordinate R c))
@[expose] def infinityQ1 : Γ(tensor R c,infinityChart R c ''ᵁ ⊤) :=
  weightedSquare (infinityChart R c) (structureMap R c) (infinityChart_structure R c)
    ((VerticalSection318.J : IntegralInfinityChart318.Order R c)^2 *
      IntegralInfinityCoefficients318.coefficient1 R c)
    (KaehlerDifferential.D R (IntegralInfinityChart318.Order R c)
      (IntegralInfinityChart318.coordinate R c))

/-- No ambient model, chart embedding, overlap route or open-immersion
hypothesis remains an input: all are supplied by the actual integral gluing. -/
theorem q0_restrictions_agree :
    (tensor R c).presheaf.map (homOfLE (branchLE R c)).op (branchQ0 R c) =
      (tensor R c).presheaf.map (homOfLE (infinityLE R c)).op (infinityQ0 R c) := by
  exact IntegralOverlapSheafCompatibility318.restrictions0_agree R c
    (overlapChart R c) (structureMap R c) (IntegralGluedChartGeometry318.overlap_over_base R c)
    (branchChart R c) (infinityChart R c) (branch_over_base R c) (infinityChart_structure R c)
    (branch_route R c) (infinity_route R c) (branchLE R c) (infinityLE R c)

theorem q1_restrictions_agree :
    (tensor R c).presheaf.map (homOfLE (branchLE R c)).op (branchQ1 R c) =
      (tensor R c).presheaf.map (homOfLE (infinityLE R c)).op (infinityQ1 R c) := by
  exact IntegralOverlapSheafCompatibility318.restrictions1_agree R c
    (overlapChart R c) (structureMap R c) (IntegralGluedChartGeometry318.overlap_over_base R c)
    (branchChart R c) (infinityChart R c) (branch_over_base R c) (infinityChart_structure R c)
    (branch_route R c) (infinity_route R c) (branchLE R c) (infinityLE R c)
end IntegralGluedTensorSections318
