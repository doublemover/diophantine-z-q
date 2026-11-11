module
public import ThreeCompactParameter318
public import LiteralPlaneComparison318
public section
noncomputable section
namespace LiteralThreeCompactParameter318
open ThreeCompactParameter318 LiteralThreePlanePoints318
open ThreeArithmeticQuotient318 LiteralPlaneComparison318
open ModularArithmeticCoordinates318 AdmissibleJLocalHomeomorph318
set_option maxHeartbeats 0

/-- The polynomial is definitionally the original admitted literal equation. -/
lemma quartic_eq_original (z x : ℂ) :
    quartic z x=LiteralThreeBaseEvaluation318.Q z x := rfl

/-- Reassociate the existing nested subtypes, preserving j and x. -/
@[expose] def planeEquiv : Plane ≃ PlaneOpen where
  toFun p := ⟨(p.val.1.val,p.val.2),p.val.1.property.1,p.val.1.property.2,p.property⟩
  invFun p := ⟨(⟨p.val.1,p.property.1,p.property.2.1⟩,p.val.2),p.property.2.2⟩
  left_inv _p := rfl
  right_inv _p := rfl

@[expose] def planeHomeomorph : Plane ≃ₜ PlaneOpen where
  toEquiv := planeEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.fst).subtype_val).prodMk continuous_subtype_val.snd
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd

/-- The actual old arithmetic plane, with an explicit global rational
parameter on its complete existing domain. No compactification is assumed. -/
@[expose] def planeParameter : Plane ≃ₜ ParameterOpen :=
  planeHomeomorph.trans openHomeomorph.symm

lemma planeParameter_apply (p : Plane) :
    (planeParameter p).val=parameter (planeJ p) (planeX p) := rfl

lemma planeParameter_inverse_j (t : ParameterOpen) :
    planeJ (planeParameter.symm t)=J t.val := rfl

lemma planeParameter_inverse_x (t : ParameterOpen) :
    planeX (planeParameter.symm t)=X t.val := rfl

/-- This consumes the original Gamma1(3) comparison. The maps are not
replaced by a point count, arbitrary labeling or transported topology. -/
@[expose] def sourceParameter (N : ℕ) [NeZero N] : Source ≃ₜ ParameterOpen :=
  (comparison N).trans planeParameter

lemma sourceParameter_apply (N : ℕ) [NeZero N] (q : Source) :
    (sourceParameter N q).val=parameter (sourceComplexJ q) (sourceX q) := by
  change parameter (planeJ (comparison N q)) (planeX (comparison N q))=_
  rw [comparison_j,comparison_x]

lemma sourceParameter_j (N : ℕ) [NeZero N] (q : Source) :
    J (sourceParameter N q).val=sourceComplexJ q := by
  have hi := planeParameter.symm_apply_apply (comparison N q)
  exact (congrArg planeJ hi).trans (comparison_j N q)

lemma sourceParameter_x (N : ℕ) [NeZero N] (q : Source) :
    X (sourceParameter N q).val=sourceX q := by
  have hi := planeParameter.symm_apply_apply (comparison N q)
  exact (congrArg planeX hi).trans (comparison_x N q)

lemma sourceParameter_inverse_j (N : ℕ) [NeZero N] (t : ParameterOpen) :
    sourceComplexJ ((sourceParameter N).symm t)=J t.val :=
  comparison_symm_j N (planeParameter.symm t)

lemma sourceParameter_inverse_x (N : ℕ) [NeZero N] (t : ParameterOpen) :
    sourceX ((sourceParameter N).symm t)=X t.val :=
  comparison_symm_x N (planeParameter.symm t)

/-- The literal affine equation has no point over the excluded elliptic
j value 1728, so extension cannot retain this single affine x chart. -/
lemma original_no_finite_point_1728 (x : ℂ) :
    LiteralThreeBaseEvaluation318.Q 1728 x ≠ 0 := by
  norm_num [LiteralThreeBaseEvaluation318.Q]

/-- At j=0 the original affine equation collapses all normalized branches
to x=0. This equality is not a normalization or reduced-fiber assertion. -/
lemma original_zero_fiber (x : ℂ) :
    LiteralThreeBaseEvaluation318.Q 0 x=0 ↔ x=0 := by
  simp [LiteralThreeBaseEvaluation318.Q]

end LiteralThreeCompactParameter318
