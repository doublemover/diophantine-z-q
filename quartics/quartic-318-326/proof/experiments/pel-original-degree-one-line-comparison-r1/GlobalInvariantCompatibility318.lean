module
public import InvariantTransition318
public import TripleOpen318
public section
noncomputable section
namespace GlobalInvariantCompatibility318
open AlgebraicGeometry CategoryTheory
open InvariantNormalizedFrames318 InvariantTransition318
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- Full actual sheaf-frame equality on the finite x/y overlap. -/
theorem finite_identifications (A B : R) :
    letI := FiniteOverlapSheaves318.x_open A B
    letI := FiniteOverlapSheaves318.y_open A B
    along (B:=FiniteInvariantDifferential318.CommonRing A B) (FiniteInvariantDifferential318.xMap A B) (xFrame A B)=
      along (B:=FiniteInvariantDifferential318.CommonRing A B) (FiniteInvariantDifferential318.yMap A B) (finiteFrame A B) := by
  letI := FiniteOverlapSheaves318.x_open A B
  letI := FiniteOverlapSheaves318.y_open A B
  exact along_eq_of_generators _ _ _ _ _ _ (x_normalized A B) (finite_normalized A B)
    (FiniteInvariantDifferential318.invariant_overlap A B).symm

/-- Full actual sheaf-frame equality on the finite/infinity overlap. -/
theorem infinity_identifications (A B : R) :
    letI := ActualInfinityOpen318.finite_open A B
    letI := ActualInfinityOpen318.infinity_open A B
    along (B:=ActualDifferentialOverlap318.CommonRing A B) (DifferentialChartMaps318.finiteChartMap A B) (finiteFrame A B)=
      along (B:=ActualDifferentialOverlap318.CommonRing A B) (DifferentialChartMaps318.infinityChartMap A B) (infinityFrame A B) := by
  letI := ActualInfinityOpen318.finite_open A B
  letI := ActualInfinityOpen318.infinity_open A B
  exact along_eq_of_generators _ _ _ _ _ _ (finite_normalized A B) (infinity_normalized A B)
    (InvariantChartForms318.invariant_overlap A B)

/-- Full genuine sheaf transition coherence on the actual three-chart localization. -/
theorem triple_identifications (A B : R) :
    letI := TripleOpen318.fromX_open A B
    letI := TripleOpen318.fromInfinity_open A B
    along (B:=ActualDifferentialTriple318.Triple A B)
      (ActualDifferentialTriple318.fromX A B) (xFrame A B)=
    along (B:=ActualDifferentialTriple318.Triple A B)
      (ActualDifferentialTriple318.fromInfinity A B) (infinityFrame A B) := by
  letI := TripleOpen318.fromX_open A B
  letI := TripleOpen318.fromInfinity_open A B
  exact along_eq_of_generators _ _ _ _ _ _ (x_normalized A B) (infinity_normalized A B)
    ((ActualDifferentialTriple318.triple_forms A B).1.trans (ActualDifferentialTriple318.triple_forms A B).2)
end GlobalInvariantCompatibility318
