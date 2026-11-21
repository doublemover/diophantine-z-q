module
public import SelectedLiteralArithmeticChart318
public import SelectedOriginalLiteralAtOne318
public import SelectedFullSimpleMonicFiber318
public import Mathlib.FieldTheory.SplittingField.Construction
public section
noncomputable section

open Polynomial NumberField
open scoped Classical
open SelectedLiteralArithmeticChart318 SelectedOriginalLiteralAtOne318
open SelectedOriginalLiteralScalarUniqueness318 SelectedFullSimpleMonicFiber318

namespace SelectedOriginalArithmeticCenterFiber318

attribute [local instance] kernelFinite kernelEtale

variable (N : ℕ) [NeZero N] (hN : 2 < N)
variable (C : Chart N hN)

abbrev specialization (L : Type*) [Field L] [CharZero L] :=
  C.p.map (atOne L N)

/-- The field of all actual centers for the already retained chart;
it is fixed before any further field chosen for semistable reduction. -/
abbrev centerField := (specialization N hN C ℚ).SplittingField

instance centerField_numberField : NumberField (centerField N hN C) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

variable (L : Type*) [Field L] [NumberField L]

theorem splits_in_actual_field (ι : centerField N hN C →+* L) :
    (specialization N hN C L).Splits := by
  let f := specialization N hN C ℚ
  let E := centerField N hN C
  have h := (SplittingField.splits f).map ι
  change (((C.p.map (atOne ℚ N)).map (algebraMap ℚ E)).map ι).Splits at h
  have he : (C.p.map (atOne ℚ N)).map (algebraMap ℚ E) = C.p.map (atOne E N) := by
    rw [Polynomial.map_map, atOne_change]
  rw [he, Polynomial.map_map, atOne_change] at h
  exact h

abbrev roots := ↥((specialization N hN C L).roots.toFinset)
abbrev evaluations :=
  {f : AdjoinRoot C.p →+* L // f (AdjoinRoot.of C.p (OpenJModel318.jCoord N)) = 1}

private theorem root_zero (x : roots N hN C L) :
    C.p.eval₂ (atOne L N) (x : L) = 0 := by
  rw [←Polynomial.eval_map]
  exact (Polynomial.IsRoot.def).mp
    (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp x.property))

def rootEvaluation (x : roots N hN C L) : evaluations N hN C L :=
  ⟨AdjoinRoot.lift (atOne L N) (x : L) (root_zero N hN C L x),
    (AdjoinRoot.lift_of (root_zero N hN C L x) (x := OpenJModel318.jCoord N)).trans (atOne_j L N)⟩

theorem rootEvaluation_root (x : roots N hN C L) :
    (rootEvaluation N hN C L x).val (AdjoinRoot.root C.p) = x.val :=
  AdjoinRoot.lift_root (root_zero N hN C L x)

private theorem same_base (f : evaluations N hN C L) :
    f.val.comp (AdjoinRoot.of C.p) = atOne L N := by
  apply over_original_j_eq
  exact f.property.trans (atOne_j L N).symm

private theorem evaluation_isRoot (f : evaluations N hN C L) :
    Polynomial.IsRoot (specialization N hN C L) (f.val (AdjoinRoot.root C.p)) := by
  have he : (C.p.map (atOne L N)).eval (f.val (AdjoinRoot.root C.p)) = 0 := by
    rw [Polynomial.eval_map, ←same_base N hN C L f]
    change C.p.eval₂ (f.val.comp (algebraMap (OpenJModel318.Base N) (AdjoinRoot C.p)))
      (f.val (AdjoinRoot.root C.p)) = 0
    rw [←Polynomial.hom_eval₂, ←Polynomial.aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  exact (Polynomial.IsRoot.def).mpr he

private def evaluationRoot (f : evaluations N hN C L) : roots N hN C L :=
  ⟨f.val (AdjoinRoot.root C.p), Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots (C.monic.map (atOne L N)).ne_zero).mpr
      (evaluation_isRoot N hN C L f))⟩

/-- Entire literal J=1 evaluation fiber, with no embedding or chosen
irreducible factor. Both directions remember the very same root x. -/
def allEvaluations : roots N hN C L ≃ evaluations N hN C L where
  toFun := rootEvaluation N hN C L
  invFun := evaluationRoot N hN C L
  left_inv x := Subtype.ext (rootEvaluation_root N hN C L x)
  right_inv f := by
    apply Subtype.ext
    apply AdjoinRoot.ringHom_ext
    · exact (AdjoinRoot.lift_comp_of (root_zero N hN C L
        (evaluationRoot N hN C L f))).trans (same_base N hN C L f).symm
    · exact rootEvaluation_root N hN C L (evaluationRoot N hN C L f)

/-- At every true extension that contains the retained splitting
field, the complete arithmetic evaluation fiber has exactly deg p
distinct entries. Both the level and the distinguished root stay fixed. -/
theorem exact_fiber_count (ι : centerField N hN C →+* L) :
    Fintype.card (roots N hN C L) = C.p.natDegree := by
  have hs := (separable_of_quotient_derivative_unit C.p C.derivativeUnit).map
    (f := atOne L N)
  have hp := splits_in_actual_field N hN C L ι
  rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hs.nodup_roots,
    ←hp.natDegree_eq_card_roots, C.monic.natDegree_map]

end SelectedOriginalArithmeticCenterFiber318

#print axioms SelectedOriginalArithmeticCenterFiber318.allEvaluations
#print axioms SelectedOriginalArithmeticCenterFiber318.exact_fiber_count
