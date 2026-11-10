module
public import ComplexTorusCoverIndex318
public import PELOriginalInvolutionActualTorus318
public section
noncomputable section
namespace PELOriginalPeriodIndex318
open PELOriginalInvolutionTower318 PELOriginalTorusCoverLift318
open ComplexLineLatticeAtlas318
variable (i:Fin 4)
local instance : PathConnectedSpace (InvolutionBase i):=original_pathConnected i

/-- The actual complete original source period subgroup inside the
actual full target lattice, not an abstract isomorphic replacement. -/
@[expose] def latticeKernel : AddSubgroup (PELOriginalCharacterTorus318.periods i):=
  (PELOriginalInvolutionActualTorus318.periods i).comap
    (PELOriginalCharacterTorus318.periods i).subtype
abbrev Fiber := {x:InvolutionBase i // torusMap i x=
  projection (PELOriginalCharacterTorus318.periods i) 0}
@[expose] def fiberEquiv :
    (PELOriginalCharacterTorus318.periods i ⧸ latticeKernel i)≃Fiber i:=
  ComplexTorusCoverIndex318.fiberEquiv _ _ (torusMap_covering i) (origin i) (origin_over_zero i)
lemma fiberEquiv_projection (a:PELOriginalCharacterTorus318.periods i) :
    (fiberEquiv i ((QuotientAddGroup.mk' (latticeKernel i)) a)).val=universalLift i a :=
  congrArg Subtype.val (ComplexTorusCoverIndex318.fiberEquiv_mk
    _ _ (torusMap_covering i) (origin i) (origin_over_zero i) a)

/-- The index FOUR is proved at the actual original fiber consumer:
the quotient of the full target lattice by the complete true source
periods is exactly the actual original residual-cover zero fiber. -/
theorem actual_index_four : (latticeKernel i).index=4 := by
  have h:=ComplexTorusCoverIndex318.index_eq_fiber
    (PELOriginalCharacterTorus318.periods i) (torusMap i)
    (torusMap_covering i) (origin i) (origin_over_zero i)
  exact h.trans (torusMap_fiber_four i (projection (PELOriginalCharacterTorus318.periods i) 0))

@[expose] def fiberTranslate (a:PELOriginalCharacterTorus318.periods i) : Fiber i≃Fiber i:=
  ComplexTorusCoverIndex318.fiberTranslate _ _ (torusMap_covering i) (origin i) (origin_over_zero i) a
lemma actual_translation (a b:PELOriginalCharacterTorus318.periods i) :
    (fiberTranslate i a (fiberEquiv i ((QuotientAddGroup.mk' (latticeKernel i)) b))).val=
      universalLift i ((b:ℂ)+(a:ℂ)) := by
  change (ComplexTorusCoverIndex318.fiberTranslate _ _ (torusMap_covering i) (origin i)
    (origin_over_zero i) a (ComplexTorusCoverIndex318.fiberEquiv _ _
      (torusMap_covering i) (origin i) (origin_over_zero i)
      ((QuotientAddGroup.mk' (latticeKernel i)) b))).val=_
  rw [ComplexTorusCoverIndex318.fiberEquiv_mk,ComplexTorusCoverIndex318.fiberTranslate_lift]
  rfl
end PELOriginalPeriodIndex318
