module
public import PELOriginalRegularCoordinateAlgebra318
public import FourRootSchemePointEquivariance318
public section
noncomputable section
namespace PELOriginalCompletedChartEvaluation318
open scoped OnePoint
open PELUnlevelledComplexBase318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318 PELOriginalMaximalQuotient318
open FourRootNormalizedPointCharts318

/-- Graphs of actual original chart coordinates. The source component is
always an original analytic point, not a substituted model point. -/
abbrev FiniteSource := {x : UnlevelledBase × FinitePoints branches //
  completedMap x.1 = finiteChart branches x.2}
abbrev InfinitySource := {x : UnlevelledBase × InfinityPoints branches //
  completedMap x.1 = infinityChart branches x.2}

lemma finite_source_injective : Function.Injective (fun x : FiniteSource => x.val.1) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext h
  apply Sum.inl_injective
  exact x.property.symm.trans ((congrArg completedMap h).trans y.property)
lemma infinity_source_injective : Function.Injective (fun x : InfinitySource => x.val.1) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext h
  apply infinityChart_injective branches
  exact x.property.symm.trans ((congrArg completedMap h).trans y.property)

theorem original_cover (p : UnlevelledBase) :
    (∃ x : FiniteSource, x.val.1 = p) ∨ (∃ x : InfinitySource, x.val.1 = p) := by
  rcases charts_cover branches (completedMap p) with ⟨q,hq⟩ | ⟨q,hq⟩
  · exact Or.inl ⟨⟨(p,q),hq.symm⟩,rfl⟩
  · exact Or.inr ⟨⟨(p,q),hq.symm⟩,rfl⟩

def finiteAt (x : FiniteSource) : FourRootAffineCoordinateRing318.Ring branches →ₐ[ℂ] ℂ :=
  (FourRootAffineCoordinateRing318.pointEquiv branches).symm x.val.2
@[expose] def infinityAt (x : InfinitySource) : FourRootInfinityCoordinateRing318.Ring branches →ₐ[ℂ] ℂ :=
  (FourRootInfinityCoordinateRing318.pointEquiv branches).symm x.val.2

/-- Public defining equation for downstream finite function-range consumers. -/
lemma finiteAt_eq (x : FiniteSource) :
    finiteAt x = (FourRootAffineCoordinateRing318.pointEquiv branches).symm x.val.2 := rfl

/-- Public defining equation for downstream infinity function-range consumers. -/
lemma infinityAt_eq (x : InfinitySource) :
    infinityAt x = (FourRootInfinityCoordinateRing318.pointEquiv branches).symm x.val.2 := rfl

/-- Regular-source restriction is literally the previously constructed
root evaluator, so this completion does not choose another generic map. -/
@[expose] def regularPoint (x : PELOriginalRegularCoordinateAlgebra318.OriginalRegular) : FiniteSource :=
  ⟨(x.val,⟨(PELOriginalContactRootFunctions318.base x.val,
    PELOriginalContactRootFunctions318.roots x.val),
    PELOriginalContactRootFunctions318.roots_square x.val x.property⟩),
    completedMap_regular x.val x.property⟩
lemma regular_agreement (x : PELOriginalRegularCoordinateAlgebra318.OriginalRegular) :
    finiteAt (regularPoint x) = PELOriginalRegularCoordinateAlgebra318.atPoint x := by
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k <;> simp [finiteAt,regularPoint,FourRootAffineCoordinateRing318.pointEquiv,
    PELOriginalRegularCoordinateAlgebra318.atPoint_base,
    PELOriginalRegularCoordinateAlgebra318.atPoint_root]

/-- Every finite branch value is the analytic extension of the original
roots, rather than an independently selected algebraic root tuple. -/
def branchPoint (p : UnlevelledBase)
    (hp : p ∈ PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (j : Fin 4)
    (h : PELOriginalContactBranchSquare318.normalizedMap p = (branches j : OnePoint ℂ)) :
    FiniteSource :=
  ⟨(p,finiteCenter p hp j h),completedMap_finiteBranch p hp j h⟩
lemma branch_root_value (p : UnlevelledBase)
    (hp : p ∈ PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (j : Fin 4) (h : PELOriginalContactBranchSquare318.normalizedMap p = (branches j : OnePoint ℂ))
    (k : Fin 4) :
    finiteAt (branchPoint p hp j h) (FourRootAffineCoordinateRing318.coordinate branches (some k)) =
      finiteRoots p hp j h k 0 := by
  simp [finiteAt,branchPoint,FourRootAffineCoordinateRing318.pointEquiv,finiteCenter]

/-- All eight actual infinity centers retain their normalized sign ratios. -/
def infinityCenterPoint (p : UnlevelledBase)
    (hp : p ∈ PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (h : PELOriginalContactBranchSquare318.normalizedMap p = ∞) : InfinitySource :=
  ⟨(p,FourRootCompletedSchemePoints318.center branches (infinityCenter p hp h)),by
    rw [completedMap_infinity p hp h]
    exact (infinityChart_zero branches (infinityCenter p hp h)).symm⟩
lemma infinity_parameter_zero (p : UnlevelledBase)
    (hp : p ∈ PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (h : PELOriginalContactBranchSquare318.normalizedMap p = ∞) :
    infinityAt (infinityCenterPoint p hp h) (FourRootInfinityCoordinateRing318.coordinate branches none) = 0 := by
  simp [infinityAt,infinityCenterPoint,FourRootInfinityCoordinateRing318.pointEquiv,
    FourRootCompletedSchemePoints318.center]
lemma infinity_ratio_value (p : UnlevelledBase)
    (hp : p ∈ PELOriginalBranchLabels318.nontrivialStabilizerLocus)
    (h : PELOriginalContactBranchSquare318.normalizedMap p = ∞) (k : Fin 4) :
    infinityAt (infinityCenterPoint p hp h) (FourRootInfinityCoordinateRing318.coordinate branches (some k)) =
      (infinityCenter p hp h).val k := by
  simp [infinityAt,infinityCenterPoint,FourRootInfinityCoordinateRing318.pointEquiv,
    FourRootCompletedSchemePoints318.center]

/-- These evaluators give the same whole original Scheme-valued points;
this is not an algebraization assertion about the original source. -/
lemma finite_comparison (x : FiniteSource) :
    PELOriginalContactSchemePoints318.comparison x.val.1 =
      FourRootCompletedSchemePoints318.finitePoint branches x.val.2 :=
  PELOriginalContactSchemePoints318.finite_value x.property
lemma infinity_comparison (x : InfinitySource) :
    PELOriginalContactSchemePoints318.comparison x.val.1 =
      FourRootCompletedSchemePoints318.infinityPoint branches x.val.2 := by
  rw [PELOriginalContactSchemePoints318.comparison_value,x.property]
  exact FourRootCompletedSchemePoints318.completed_infinity branches x.val.2

lemma finite_base (x : FiniteSource) :
    FourRootNormalizedPointCharts318.projection branches (finiteChart branches x.val.2) =
      PELOriginalContactBranchSquare318.normalizedMap x.val.1 :=
  x.property ▸ projection_commutes x.val.1
lemma infinity_base (x : InfinitySource) :
    FourRootNormalizedPointCharts318.projection branches (infinityChart branches x.val.2) =
      PELOriginalContactBranchSquare318.normalizedMap x.val.1 :=
  x.property ▸ projection_commutes x.val.1

def finiteAction (g : Labels) (x : FiniteSource) : FiniteSource :=
  ⟨(g • x.val.1,FourRootNormalizedSignAction318.finite branches
      (OriginalContactInertiaBasis318.basis g) x.val.2),by
    rw [PELOriginalCompletedContactDeck318.equivariant,x.property]
    exact FourRootNormalizedSignAction318.finite_chart _ _ _⟩
def infinityAction (g : Labels) (x : InfinitySource) : InfinitySource :=
  ⟨(g • x.val.1,FourRootNormalizedSignAction318.infinity branches
      (OriginalContactInertiaBasis318.basis g) x.val.2),by
    rw [PELOriginalCompletedContactDeck318.equivariant,x.property]
    exact FourRootNormalizedSignAction318.infinity_chart _ _ _⟩

lemma finite_deck (g : Labels) (x : FiniteSource) :
    finiteAt (finiteAction g x) = (finiteAt x).comp
      (FourRootCoordinateRingSigns318.finiteEnd branches (OriginalContactInertiaBasis318.basis g)) := by
  apply (FourRootAffineCoordinateRing318.pointEquiv branches).injective
  rw [Equiv.apply_symm_apply]
  exact (FourRootCoordinateRingSigns318.finite_point branches _ (finiteAt x)).symm
lemma infinity_deck (g : Labels) (x : InfinitySource) :
    infinityAt (infinityAction g x) = (infinityAt x).comp
      (FourRootCoordinateRingSigns318.infinityEnd branches (OriginalContactInertiaBasis318.basis g)) := by
  apply (FourRootInfinityCoordinateRing318.pointEquiv branches).injective
  rw [Equiv.apply_symm_apply]
  exact (FourRootCoordinateRingSigns318.infinity_point branches _ (infinityAt x)).symm
/-- Both chart evaluators reconstruct the same actual original complex
Scheme point on their intersection. A sheaf-level gluing is NOT inferred
from this pointwise identity. -/
lemma overlap_comparison (x : FiniteSource) (y : InfinitySource)
    (h : x.val.1 = y.val.1) :
    FourRootCompletedSchemePoints318.finitePoint branches x.val.2 =
      FourRootCompletedSchemePoints318.infinityPoint branches y.val.2 :=
  (finite_comparison x).symm.trans
    ((congrArg PELOriginalContactSchemePoints318.comparison h).trans (infinity_comparison y))
end PELOriginalCompletedChartEvaluation318
