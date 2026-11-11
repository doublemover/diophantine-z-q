module
public import PELOriginalThetaParityReindex318
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public section
noncomputable section
namespace PELOriginalThetaAddition318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalLevelTheta318
open PELOriginalThetaParityReindex318
variable (τ:ℂ) (hτ:0<τ.im)
lemma original_norm_summable (z:ComplexVectors):Summable (fun k:Index=>‖term τ k z‖):=by
  let S:=max |(z 0).im| |(z 1).im|
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (norm_bound τ hτ S z (le_max_left _ _) (le_max_right _ _)) (bound_summable τ hτ S)
lemma scaled_norm_summable (z:ComplexVectors):
    Summable (fun k:Index=>‖PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) k z‖):=by
  let S:=max |(z 0).im| |(z 1).im|
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (PELOriginalScaledThetaConvergence318.norm_bound τ hτ (1/(2:ℝ)) (by norm_num)
      S z (le_max_left _ _) (le_max_right _ _))
    (PELOriginalScaledThetaConvergence318.bound_summable τ hτ (1/(2:ℝ)) (by norm_num) S)
lemma fiber_series (r:Label 2) (z:ComplexVectors):
    (∑'k:ResidueFiber r,PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) k.val z)=
      levelTheta τ 2 r z:=by
  rw [tsum_subtype]
  rfl
@[expose] def pairedSummand (z a:ComplexVectors)
    (p:Σr:Label 2,ResidueFiber r×ResidueFiber r):ℂ:=
  PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) p.2.1.val z*
    PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) p.2.2.val a
lemma paired_summable (z a:ComplexVectors):Summable (pairedSummand τ z a):=by
  apply completeEquiv.summable_iff.mp
  have h:=summable_mul_of_summable_norm
    (original_norm_summable τ hτ (z+a)) (original_norm_summable τ hτ (z-a))
  apply h.congr
  intro p
  exact summand_identity τ p.1 p.2 z a
lemma paired_fiber_sum (r:Label 2) (z a:ComplexVectors):
    (∑'p:ResidueFiber r×ResidueFiber r,pairedSummand τ z a ⟨r,p⟩)=
      levelTheta τ 2 r z*levelTheta τ 2 r a:=by
  have hz:Summable (fun k:ResidueFiber r=>
      ‖PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) k.val z‖):=
    (scaled_norm_summable τ hτ z).subtype _
  have ha:Summable (fun k:ResidueFiber r=>
      ‖PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) k.val a‖):=
    (scaled_norm_summable τ hτ a).subtype _
  rw [←fiber_series τ r z,←fiber_series τ r a]
  exact (tsum_mul_tsum_of_summable_norm hz ha).symm

/-- Exact genus-two addition formula with FOUR concrete parity labels.
All products, regroupings and reindexings use genuine absolute summability
and an explicit bijection of the entire integer lattices. -/
theorem addition (z a:ComplexVectors):
    theta τ (z+a)*theta τ (z-a)=
      ∑r:Label 2,levelTheta τ 2 r z*levelTheta τ 2 r a:=by
  calc
    _ = ∑'p:Index×Index,term τ p.1 (z+a)*term τ p.2 (z-a) :=
      tsum_mul_tsum_of_summable_norm (original_norm_summable τ hτ (z+a))
        (original_norm_summable τ hτ (z-a))
    _ = ∑'p,pairedSummand τ z a p := by
      rw [←completeEquiv.tsum_eq (pairedSummand τ z a)]
      apply tsum_congr
      intro p
      exact summand_identity τ p.1 p.2 z a
    _ = ∑'r:Label 2,∑'p:ResidueFiber r×ResidueFiber r,pairedSummand τ z a ⟨r,p⟩ :=
      (paired_summable τ hτ z a).tsum_sigma
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro r hr
      exact paired_fiber_sum τ hτ r z a
end PELOriginalThetaAddition318
