module
public import ArithmeticComparisonHomeomorph318
public import LiteralThreePlanePoints318
public import AdmissibleJComplexAtlas318
public section
noncomputable section
namespace LiteralPlaneComparison318
open ThreeArithmeticQuotient318 LiteralThreePlanePoints318
open ArithmeticPointTopology318 ModularCoordinateProper318 ModularArithmeticCoordinates318
open AdmissibleJLocalHomeomorph318 AdmissibleJComplexAtlas318
set_option maxHeartbeats 400000

/-- The original arithmetic comparison, followed by the independently checked
literal equation-algebra coordinate map. Both existing topologies are retained. -/
@[expose] def comparison (N : ℕ) [NeZero N] : Source ≃ₜ Plane :=
  (ArithmeticComparisonHomeomorph318.comparison N).trans (pointHomeomorph N)

@[expose] def planeJ (p : Plane) : ℂ := p.val.1.val
@[expose] def planeX (p : Plane) : ℂ := p.val.2

lemma comparison_coordinates (N : ℕ) [NeZero N] (q : Source) :
    (comparison N q).val=openCoordinates q := by
  change pointCoordinates N (ArithmeticComparisonHomeomorph318.comparison N q)=_
  exact ArithmeticComparisonHomeomorph318.comparison_coordinates N q

/-- Exact genuine-j compatibility of the actual composite map. -/
lemma comparison_j (N : ℕ) [NeZero N] (q : Source) :
    planeJ (comparison N q)=sourceComplexJ q := by
  exact congrArg (fun z : JOpen × ℂ => z.1.val) (comparison_coordinates N q)

lemma comparison_x (N : ℕ) [NeZero N] (q : Source) :
    planeX (comparison N q)=sourceX q := by
  exact congrArg Prod.snd (comparison_coordinates N q)

/-- The inverse has the same exact j coordinate; no target complex structure
or target chart is assumed in this identity. -/
lemma comparison_symm_j (N : ℕ) [NeZero N] (p : Plane) :
    sourceComplexJ ((comparison N).symm p)=planeJ p := by
  calc
    _=planeJ (comparison N ((comparison N).symm p)) :=
      (comparison_j N ((comparison N).symm p)).symm
    _=planeJ p := congrArg planeJ ((comparison N).apply_symm_apply p)

lemma comparison_symm_x (N : ℕ) [NeZero N] (p : Plane) :
    sourceX ((comparison N).symm p)=planeX p := by
  calc
    _=planeX (comparison N ((comparison N).symm p)) :=
      (comparison_x N ((comparison N).symm p)).symm
    _=planeX p := congrArg planeX ((comparison N).apply_symm_apply p)

lemma source_chart_comparison (N : ℕ) [NeZero N] (a q : Source) :
    localChart a q=planeJ (comparison N q) := by
  rw [localChart_apply,comparison_j]

/-- In an actual source j chart, the comparison has literal first coordinate
z on the chart target. This is a coordinate identity, not a target-atlas claim. -/
lemma comparison_chart_symm_j (N : ℕ) [NeZero N] (a : Source) (z : ℂ)
    (hz : z∈(localChart a).target) :
    planeJ (comparison N ((localChart a).symm z))=z := by
  rw [comparison_j,←localChart_apply a ((localChart a).symm z)]
  exact (localChart a).right_inv hz

/-- The original comparison recovers a target point from this actual local
source inverse precisely on its already proved source neighborhood. -/
lemma comparison_chart_recovery (N : ℕ) [NeZero N] (a : Source) (p : Plane)
    (hp : (comparison N).symm p∈(localChart a).source) :
    comparison N ((localChart a).symm (planeJ p))=p := by
  have hj : planeJ p=localChart a ((comparison N).symm p) := by
    rw [localChart_apply,comparison_symm_j]
  rw [hj,(localChart a).left_inv hp,(comparison N).apply_symm_apply]

lemma comparison_projection_j (N : ℕ) [NeZero N] (tau : Locus) :
    planeJ (comparison N (sourceProjection tau))=ActualQJ318.jInvariant tau.val := by
  rw [comparison_j,sourceComplexJ_projection]

end LiteralPlaneComparison318
