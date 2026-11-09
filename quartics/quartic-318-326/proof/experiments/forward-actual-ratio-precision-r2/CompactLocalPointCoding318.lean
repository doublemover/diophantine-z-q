module
public import LocalPointDifference318
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement
public section
noncomputable section
namespace CompactLocalPointCoding318
open Set Filter ReciprocalDouble318 WeierstrassCurve.Affine
open LocalDerivativeSeparation318 LocalPointDifference318
open scoped Topology
set_option maxHeartbeats 1000000
variable {F : Type*} [NormedField F] [CharZero F] [DecidableEq F]

@[expose] def integralCurve (D : F) : Set (F×F) :=
  {z | ‖z.1‖≤1 ∧ ‖z.2‖≤1 ∧ z.2^2=z.1^3-D*z.1}

lemma integralCurve_compact [ProperSpace F] (D : F) : IsCompact (integralCurve D) := by
  have hc : IsClosed {z : F×F | z.2^2=z.1^3-D*z.1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hk := ((isCompact_closedBall (0:F) 1).prod
    (isCompact_closedBall (0:F) 1)).inter_right hc
  convert hk using 1
  ext z
  simp only [integralCurve,mem_setOf_eq,mem_inter_iff,mem_prod,
    Metric.mem_closedBall,dist_zero_right]
  tauto

lemma curve_nonsingular (D : F) (hD : D≠0) (z : integralCurve D) :
    (E D).Nonsingular z.1.1 z.1.2 := by
  rw [nonsingular_iff']
  constructor
  · rw [equation_iff]
    simpa only [E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using z.2.2.2
  · rcases derivative_or_ordinate D z.1.1 z.1.2 hD z.2.2.2 with hy|hg
    · right
      simpa only [E,zero_mul,add_zero] using mul_ne_zero (show (2:F)≠0 by norm_num) hy
    · left
      simpa only [E,zero_mul,mul_zero,zero_sub,zero_add,add_zero,
        neg_ne_zero,sub_eq_add_neg] using hg

@[expose] def curvePoint (D : F) (hD : D≠0) (z : integralCurve D) : (E D).Point :=
  Point.some z.1.1 z.1.2 (curve_nonsingular D hD z)

@[expose] def radius (D : F) (z : F×F) : ℝ :=
  max ‖2*z.2‖ ‖3*z.1^2-D‖

lemma radius_pos (D : F) (hD : D≠0) (z : integralCurve D) : 0<radius D z := by
  rcases derivative_or_ordinate D z.1.1 z.1.2 hD z.2.2.2 with hy|hg
  · exact (norm_pos_iff.mpr (mul_ne_zero (by norm_num) hy)).trans_le (le_max_left _ _)
  · exact (norm_pos_iff.mpr hg).trans_le (le_max_right _ _)

/-- A genuine metric ball of original affine coordinates is contained in a
single coset of the actual formal subgroup. Both derivative charts and the
same-x tangent branch are supplied by close_points. -/
theorem nearby_difference (hna : IsNonarchimedean (NormedField.toAbsoluteValue F))
    (D : F) (hD : D≠0) (hDi : ‖D‖≤1) (z t : integralCurve D)
    (ht : (t:F×F)∈Metric.ball (z:F×F) (radius D z)) :
    curvePoint D hD z-curvePoint D hD t∈
      AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi := by
  have hd : max ‖t.1.1-z.1.1‖ ‖t.1.2-z.1.2‖<radius D z := by
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_eq_norm] using ht
  apply close_points (NormedField.toAbsoluteValue F) hna D z.1.1 z.1.2 t.1.1 t.1.2
    hDi (curve_nonsingular D hD z) (curve_nonsingular D hD t) z.2.1 t.2.1
  change (‖t.1.1-z.1.1‖<‖2*z.1.2‖ ∧ ‖t.1.2-z.1.2‖<‖2*z.1.2‖) ∨
    (‖t.1.1-z.1.1‖<‖3*z.1.1^2-D‖ ∧ ‖t.1.2-z.1.2‖<‖3*z.1.1^2-D‖)
  rcases le_total ‖2*z.1.2‖ ‖3*z.1.1^2-D‖ with he|he
  · right
    simpa only [radius,max_eq_right he,max_lt_iff] using hd
  · left
    simpa only [radius,max_eq_left he,max_lt_iff] using hd

/-- Compactness produces finitely many actual coset representatives. No
finite-index or residue-field conclusion is assumed as an input. -/
theorem finite_affine_codes [ProperSpace F]
    (hna : IsNonarchimedean (NormedField.toAbsoluteValue F))
    (D : F) (hD : D≠0) (hDi : ‖D‖≤1) :
    let H := AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi
    (Set.range (fun z : integralCurve D => QuotientAddGroup.mk' H (curvePoint D hD z))).Finite := by
  dsimp only
  let H := AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi
  let q := QuotientAddGroup.mk' H
  obtain ⟨s,hs⟩ := (integralCurve_compact D).elim_nhds_subcover'
    (fun z _ => Metric.ball z (radius D z))
    (fun z hz => Metric.ball_mem_nhds z (radius_pos D hD ⟨z,hz⟩))
  apply ((s.finite_toSet).image (fun z : integralCurve D => q (curvePoint D hD z))).subset
  rintro _ ⟨z,rfl⟩
  obtain ⟨t,ht,hzt⟩ := Set.mem_iUnion₂.mp (hs z.2)
  refine ⟨t,ht,?_⟩
  have hdiff := nearby_difference hna D hD hDi t z hzt
  have hz : q (curvePoint D hD t-curvePoint D hD z)=0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr hdiff
  rw [map_sub,sub_eq_zero] at hz
  exact hz

/-- Every nonformal point has integral original coordinates; the formal
coset and the compact affine codes cover the whole quotient. -/
theorem finite_formal_quotient [ProperSpace F]
    (hna : IsNonarchimedean (NormedField.toAbsoluteValue F))
    (D : F) (hD : D≠0) (hDi : ‖D‖≤1) :
    let H := AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi
    Finite ((E D).Point ⧸ H) := by
  dsimp only
  let H := AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi
  let q := QuotientAddGroup.mk' H
  let codes := Set.range (fun z : integralCurve D => q (curvePoint D hD z))
  have hc : codes.Finite := finite_affine_codes hna D hD hDi
  apply Set.finite_univ_iff.mp
  apply (hc.insert 0).subset
  intro a _
  obtain ⟨P,rfl⟩ := QuotientAddGroup.mk'_surjective H a
  by_cases hp : P∈H
  · have he : q P=0 := (QuotientAddGroup.eq_zero_iff _).mpr hp
    rw [he]
    exact Set.mem_insert 0 codes
  · apply Set.mem_insert_of_mem
    cases P with
    | zero => exact False.elim (hp (AddSubgroup.zero_mem H))
    | some x y h =>
      have hx : ‖x‖≤1 := by
        by_contra! he
        apply hp
        exact Or.inr (by simpa only [Point.xRep_some,Matrix.cons_val_zero] using he)
      have hy : ‖y‖≤1 := ordinate_integral (NormedField.toAbsoluteValue F) hna D x y hDi hx
        (FormalChartDouble.ordinate_equation D x y h)
      exact ⟨⟨(x,y),hx,hy,FormalChartDouble.ordinate_equation D x y h⟩,rfl⟩

/-- An actual positive orbit multiple enters the formal subgroup over a
proper nonarchimedean normed field, including bad reduction for nonzero D. -/
theorem orbit_entry [ProperSpace F]
    (hna : IsNonarchimedean (NormedField.toAbsoluteValue F))
    (D : F) (hD : D≠0) (hDi : ‖D‖≤1) (P : (E D).Point) :
    ∃ n : ℕ, 0<n ∧ n • P∈
      AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi := by
  let H := AlgebraicFormalSubgroup318.formalSubgroup (NormedField.toAbsoluteValue F) hna D hDi
  let q := QuotientAddGroup.mk' H
  letI := finite_formal_quotient hna D hD hDi
  obtain ⟨n,hn,hzero⟩ := (isOfFinAddOrder_of_finite (q P)).exists_nsmul_eq_zero
  refine ⟨n,hn,(QuotientAddGroup.eq_zero_iff _).mp ?_⟩
  simpa only [map_nsmul] using hzero

end CompactLocalPointCoding318
