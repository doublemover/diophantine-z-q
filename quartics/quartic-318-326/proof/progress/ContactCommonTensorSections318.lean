module
public import ContactOverlapIntrinsic318
public import ContactInfinityOverlapDifferential318
public section
noncomputable section
namespace ContactCommonTensorSections318
open AlgebraicGeometry CategoryTheory
open ContactOverlapIntrinsic318 ContactFiniteOverlapDifferential318 ContactOverlapAlgebraMaps318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def infinityQ0 :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (infinityMap c (ContactBicanonicalCoefficients318.infinityQ0 c))
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.u c))

/-- Actual common-open tensor equality for every finite branch and infinity. -/
theorem finite_infinity_q0 (i : Fin 4) : finiteQ0 c i=infinityQ0 c := by
  exact IntrinsicTensorChartSections318.weightedSquare_agreement
    (R:=ℚ) (S:=O c) (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (P c)
    (branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i)) (factor c i)
    (infinityMap c (ContactBicanonicalCoefficients318.infinityQ0 c))
      (ContactInfinityOverlapDifferential318.factor c)
    (KaehlerDifferential.D ℚ (O c) (z c i))
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.u c))
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.t c))
    (P_unit c) (coefficient_cleared c i) (ContactInfinityOverlapDifferential318.coefficient_cleared c)
    (differential_relation c i) (ContactInfinityOverlapDifferential318.differential_relation c)

@[expose] def finiteQ1 (i : Fin 4) :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (branchMap c i (ContactBicanonicalCoefficients318.branchQ1 c i))
    (KaehlerDifferential.D ℚ (O c) (z c i))
@[expose] def infinityQ1 :=
  IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c)
    (infinityMap c (ContactBicanonicalCoefficients318.infinityQ1 c))
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.u c))
@[expose] def tFunction : Γ(ContactGlobalSmooth318.Model c,embedding c ''ᵁ ⊤) :=
  ((embedding c).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (O c))).inv
    (SourceInfinityOverlap318.t c))

theorem finiteQ1_relation (i : Fin 4) : finiteQ1 c i=tFunction c • finiteQ0 c i := by
  have h : branchMap c i (ContactBicanonicalCoefficients318.branchQ1 c i)=
      SourceInfinityOverlap318.t c*branchMap c i (ContactBicanonicalCoefficients318.branchQ0 c i) := by
    rw [ContactBicanonicalCoefficients318.branchQ1,map_mul,branchMap_coordinate]
  exact (congrArg (fun a => IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c) a
    (KaehlerDifferential.D ℚ (O c) (z c i))) h).trans
      (IntrinsicTensorChartSections318.weightedSquare_mul _ _ _ _ _ _)

theorem infinityQ1_relation : infinityQ1 c=tFunction c • infinityQ0 c := by
  exact (congrArg (fun a => IntrinsicTensorChartSections318.weightedSquare (R:=ℚ) (S:=O c)
    (embedding c) (ContactIntrinsicDifferentials318.structureMap c) (over_Q c) a
    (KaehlerDifferential.D ℚ (O c) (SourceInfinityOverlap318.u c)))
      (ContactInfinityOverlapDifferential318.q1_relation c).symm).trans
        (IntrinsicTensorChartSections318.weightedSquare_mul _ _ _ _ _ _)

theorem finiteQ1_eq (i j : Fin 4) : finiteQ1 c i=finiteQ1 c j :=
  (finiteQ1_relation c i).trans ((congrArg (fun v => tFunction c • v) (finiteQ0_eq c i j)).trans
    (finiteQ1_relation c j).symm)

theorem finite_infinity_q1 (i : Fin 4) : finiteQ1 c i=infinityQ1 c :=
  (finiteQ1_relation c i).trans
    ((congrArg (fun v => tFunction c • v) (finite_infinity_q0 c i)).trans
      (infinityQ1_relation c).symm)
end ContactCommonTensorSections318
