module
public import ContactFiniteOverlapDifferential318
public import IntrinsicTensorChartSections318
public section
noncomputable section
namespace ContactOverlapIntrinsic318
open AlgebraicGeometry CategoryTheory ContactFiniteOverlapDifferential318
set_option maxHeartbeats 160000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def embedding := ContactProjectiveModel318.sourceOpen c
instance embedding_open : IsOpenImmersion (embedding c) := ContactProjectiveModel318.sourceOpen_open c

theorem over_Q : embedding c ≫ ContactIntrinsicDifferentials318.structureMap c=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (O c))) := by
  change ContactProjectiveModel318.sourceOpen c ≫ ContactIntrinsicDifferentials318.structureMap c=_
  rw [←BranchFullOverlap318.branch_square c 0,Category.assoc,
    ContactIntrinsicFrames318.branch_structure,BranchFullOverlap318.branchInclusion,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (RingHom.map_rat_algebraMap (BranchOverlapLocalization318.toOpen c 0))

/-- Actual common-open intrinsic tensor section obtained from branch i. -/
@[expose] def finiteQ0 (i : Fin 4) :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (ContactOverlapAlgebraMaps318.branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i))
    (KaehlerDifferential.D ℚ (O c) (z c i))

/-- All four finite expressions agree as actual intrinsic tensor sections
on the entire common open, by cancellation of the actual quartic unit. -/
theorem finiteQ0_eq (i j : Fin 4) : finiteQ0 c i=finiteQ0 c j := by
  exact IntrinsicTensorChartSections318.weightedSquare_agreement
    (R:=ℚ) (S:=O c) (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (P c)
    (ContactOverlapAlgebraMaps318.branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i)) (factor c i)
    (ContactOverlapAlgebraMaps318.branchMap c j (ContactBicanonicalCoefficients318.branchQ0 c j)) (factor c j)
    (KaehlerDifferential.D ℚ (O c) (z c i))
    (KaehlerDifferential.D ℚ (O c) (z c j))
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.t c))
    (P_unit c) (coefficient_cleared c i) (coefficient_cleared c j)
    (differential_relation c i) (differential_relation c j)
end ContactOverlapIntrinsic318
