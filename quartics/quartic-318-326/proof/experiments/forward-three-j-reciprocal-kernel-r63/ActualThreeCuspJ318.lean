module
public import ActualThreeCuspHomeomorph318
public import ActualThreeCuspWidths318
public import AllCuspQJ318
public import Mathlib.Analysis.Meromorphic.Order
public section
noncomputable section
open Function Filter Topology
open scoped MatrixGroups
namespace ActualThreeCuspJ318
open ActualThreeCuspHomeomorph318 WidthQParameter318 RotatedProjection318
open GammaOneAtlas318 QuotientJ318
set_option maxHeartbeats 0

abbrev natWidth (g : SL(2,ℤ)) : ℕ := RotatedWidths318.width 3 (by decide) g

/-- The exact j expression in each genuine width-q cusp chart, now proved
at level three without importing a high-level chart or filling assumption. -/
theorem j_in_coordinate (g : SL(2,ℤ)) (q : punctured (wReal g) 2) :
    jMap 3 ((cuspHomeomorph g).symm q).val=
      ActualQJ318.G (q.val^natWidth g)/(q.val^natWidth g) := by
  obtain ⟨tau,rfl⟩ := qMap_surjective (wReal g) 2 (wReal_pos g) (by norm_num) q
  rw [←cuspHomeomorph_projection g tau,Homeomorph.symm_apply_apply]
  change jMap 3 (quotientMap 3 (g•tau.val))=_
  rw [AllCuspQJ318.j_rotated]
  have he : ((cuspHomeomorph g) (projection 3 g tau)).val^natWidth g=
      Periodic.qParam 1 tau := by
    rw [cuspHomeomorph_projection]
    exact AllCuspQJ318.qParam_pow _ (RotatedWidths318.width_positive 3 (by decide) g) tau
  rw [he,ActualQJ318.G_qParam]
  field_simp [Periodic.qParam_ne_zero (tau:ℂ)]

@[expose] def jExpression (g : SL(2,ℤ)) (q : ℂ) : ℂ :=
  ActualQJ318.G (q^natWidth g)/(q^natWidth g)

lemma leading_analytic (g : SL(2,ℤ)) :
    AnalyticAt ℂ (fun q => ActualQJ318.G (q^natWidth g)) 0 := by
  have hG : AnalyticAt ℂ ActualQJ318.G 0 :=
    ActualQJ318.G_holomorphic.analyticOnNhd Metric.isOpen_ball 0 (by simp)
  have hz : (0:ℂ)^natWidth g=0 :=
    zero_pow (Nat.ne_of_gt (RotatedWidths318.width_positive 3 (by decide) g))
  rw [←hz] at hG
  exact hG.comp (f:=fun q : ℂ => q^natWidth g) (x:=0) (analyticAt_id.pow _)

lemma leading_value (g : SL(2,ℤ)) : ActualQJ318.G ((0:ℂ)^natWidth g)=1 := by
  rw [zero_pow (Nat.ne_of_gt (RotatedWidths318.width_positive 3 (by decide) g)),ActualQJ318.G_zero]

/-- Exact pole order in the actual q coordinate, not a rational target
parameter guessed to be a cusp chart. -/
theorem j_order (g : SL(2,ℤ)) : meromorphicOrderAt (jExpression g) 0 = -(natWidth g:ℤ) := by
  have hm : MeromorphicAt (jExpression g) 0 :=
    (leading_analytic g).meromorphicAt.div (analyticAt_id.pow _).meromorphicAt
  apply (meromorphicOrderAt_eq_int_iff hm).mpr
  refine ⟨fun q => ActualQJ318.G (q^natWidth g),leading_analytic g,?_,?_⟩
  · change ActualQJ318.G ((0:ℂ)^natWidth g) ≠ 0
    rw [leading_value];exact one_ne_zero
  · exact Filter.Eventually.of_forall (fun q => by
      simp [jExpression,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm])

theorem infinity_order : meromorphicOrderAt (jExpression 1) 0 = -1 := by
  rw [j_order,show natWidth 1=1 from ActualThreeCuspWidths318.width_identity]
  norm_num

theorem S_order : meromorphicOrderAt (jExpression ModularGroup.S) 0 = -3 := by
  rw [j_order,show natWidth ModularGroup.S=3 from ActualThreeCuspWidths318.width_S]
  norm_num

end ActualThreeCuspJ318
