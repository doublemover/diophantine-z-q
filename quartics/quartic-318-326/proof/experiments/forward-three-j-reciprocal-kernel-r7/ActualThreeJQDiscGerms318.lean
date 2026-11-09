module
public import ThreeJManifoldHolomorphy318
public section
noncomputable section
open Function Filter Topology
namespace ActualThreeJQDiscGerms318
open ProjectiveLineFieldPoints318 ProjectiveLinePointEquiv318 ProjectiveLineComplexTopology318
open ActualThreeProjectivePoints318 ActualThreeCompactJPoints318 ActualThreeCuspFilling318
open ActualThreeCuspExhaustion318 ActualThreeCuspAnalytic318 ActualThreeFilledHolomorphic318
open ActualThreeCuspOverlap318 ActualThreeFilledParameter318 ActualThreeSphereCharts318
open ThreeJManifoldHolomorphy318 ThreeJAnalyticGerms318 ThreeJChartHolomorphy318
open ThreeProjectiveJPoints318 SphereInversion318 FiniteCuspEnds318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : TopologicalSpace ComplexPoints := complexPointTopology

@[expose] def sourceIndex (c : End 3) : Fin 2 := if c=infinityEnd then 0 else 1
@[expose] def qGerm (c : End 3) (q : ℂ) : ℂ :=
  if c=infinityEnd then reciprocalPole (endCoordinate c q)
    else finitePole (endCoordinate c q)
@[expose] def qOrder (c : End 3) : ℕ := if c=infinityEnd then 1 else 3

lemma point_inverseSphere (c : End 3) (t : ℂ) :
    pointHomeomorph (inverseSphereChart c t)=chartPoint (R:=ℚ) (sourceIndex c) t := by
  rcases end_exhaustion c with rfl | rfl
  · simp only [sourceIndex,ite_true]
    change pointMap (R:=ℚ) (inverseSphereChart infinityEnd t)=chartPoint (R:=ℚ) 0 t
    have he : inverseSphereChart infinityEnd t=inversion (t : OnePoint ℂ) := by
      simp only [inverseSphereChart,ite_true,inversion,OnePoint.elim_some]
    rw [he]
    exact pointMap_inversion t
  · simp only [inverseSphereChart,sourceIndex,ends_distinct.symm,ite_false]
    rfl

/-- The actual selected source q-disc, not merely the transported sphere
coordinate, has this exact original algebraic chart expression near its origin. -/
lemma source_point_expression (c : End 3) :
    ∀ᶠ q in 𝓝 (0:ℂ), compactPointHomeomorph (sourceDisc c q)=
      chartPoint (R:=ℚ) (sourceIndex c) (endCoordinate c q) := by
  have hd : ∀ᶠ q in 𝓝 (0:ℂ), q ∈ disc c :=
    (disc_open c).mem_nhds (zeroPoint c).property
  filter_upwards [hd] with q hq
  rw [sourceDisc,dite_eq_left hq,compactPointHomeomorph_apply,compactHomeomorph_apply,
    filledParameter_disc,sphereChart_eq_inverse c hq,point_inverseSphere]

lemma qGerm_of_infinity (c : End 3) (hc : c=infinityEnd) :
    qGerm c=reciprocalPole ∘ endCoordinate c := by
  funext q
  exact if_pos hc

lemma qGerm_of_not_infinity (c : End 3) (hc : c≠infinityEnd) :
    qGerm c=finitePole ∘ endCoordinate c := by
  funext q
  exact if_neg hc

lemma qGerm_analytic (c : End 3) : AnalyticAt ℂ (qGerm c) 0 := by
  by_cases hc : c=infinityEnd
  · rw [qGerm_of_infinity c hc]
    exact reciprocal_cusp_germ.1.comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)
  · rw [qGerm_of_not_infinity c hc]
    exact finite_cusp_germ.1.comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)

lemma qGerm_zero (c : End 3) : qGerm c 0=0 := by
  simp only [qGerm,endCoordinate_zero,finite_cusp_germ.2.1,reciprocal_cusp_germ.2.1,ite_self]

/-- The orders survive composition with the actual source q-coordinate
because that coordinate is independently proved to have order one. -/
lemma qGerm_order (c : End 3) : meromorphicOrderAt (qGerm c) 0=(qOrder c : ℤ) := by
  have hf := (endCoordinate_analytic c).meromorphicAt
  have hF : AnalyticAt ℂ (finiteN ∘ endCoordinate c) 0 :=
    (finiteN_analytic 0).comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)
  have hR : AnalyticAt ℂ (reciprocalN ∘ endCoordinate c) 0 :=
    (reciprocalN_analytic 0).comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)
  have hFo : meromorphicOrderAt (finiteN ∘ endCoordinate c) 0=0 := by
    rw [hF.meromorphicOrderAt_eq,hF.analyticOrderAt_eq_zero.mpr
      (by simpa only [Function.comp_apply,endCoordinate_zero] using finiteN_zero_ne)]
    rfl
  have hRo : meromorphicOrderAt (reciprocalN ∘ endCoordinate c) 0=0 := by
    rw [hR.meromorphicOrderAt_eq,hR.analyticOrderAt_eq_zero.mpr
      (by simpa only [Function.comp_apply,endCoordinate_zero] using reciprocalN_zero_ne)]
    rfl
  by_cases hc : c=infinityEnd
  · rw [qGerm_of_infinity c hc,qOrder,if_pos hc]
    change meromorphicOrderAt (endCoordinate c / (reciprocalN ∘ endCoordinate c)) 0=1
    rw [meromorphicOrderAt_div hf hR.meromorphicAt,endCoordinate_order,hRo,sub_zero]
  · rw [qGerm_of_not_infinity c hc,qOrder,if_neg hc]
    change meromorphicOrderAt ((endCoordinate c)^3 / (finiteN ∘ endCoordinate c)) 0=3
    rw [meromorphicOrderAt_div (hf.pow 3) hF.meromorphicAt,
      meromorphicOrderAt_pow hf,endCoordinate_order,hFo]
    norm_num

/-- Equality of actual scheme-valued maps on a full neighborhood of every
selected q-disc origin, including the origin itself. -/
lemma qDisc_map_expression (c : End 3) :
    ∀ᶠ q in 𝓝 (0:ℂ), compactJ (sourceDisc c q)=chartPoint (R:=ℚ) 0 (qGerm c q) := by
  have hF : ∀ᶠ q in 𝓝 (0:ℂ), finiteN (endCoordinate c q) ≠ 0 := by
    have h : AnalyticAt ℂ (finiteN ∘ endCoordinate c) 0 :=
      (finiteN_analytic 0).comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)
    exact h.continuousAt.eventually_ne (by simpa only [Function.comp_apply,endCoordinate_zero] using finiteN_zero_ne)
  have hR : ∀ᶠ q in 𝓝 (0:ℂ), reciprocalN (endCoordinate c q) ≠ 0 := by
    have h : AnalyticAt ℂ (reciprocalN ∘ endCoordinate c) 0 :=
      (reciprocalN_analytic 0).comp_of_eq (endCoordinate_analytic c) (endCoordinate_zero c)
    exact h.continuousAt.eventually_ne (by simpa only [Function.comp_apply,endCoordinate_zero] using reciprocalN_zero_ne)
  filter_upwards [source_point_expression c,hF,hR] with q hq hFq hRq
  unfold compactJ
  rw [hq]
  by_cases hc : c=infinityEnd
  · simp only [sourceIndex,qGerm,if_pos hc]
    exact reciprocal_numerator_formula _ hRq
  · simp only [sourceIndex,qGerm,if_neg hc]
    exact finite_numerator_formula _ hFq

/-- The genuine reciprocal target-chart expression on the original q-disc. -/
@[expose] def actualQExpression (c : End 3) (q : ℂ) : ℂ :=
  evaluationChart 0 (compactJ (sourceDisc c q))

lemma actualQExpression_eq (c : End 3) : actualQExpression c =ᶠ[𝓝 (0:ℂ)] qGerm c := by
  filter_upwards [qDisc_map_expression c] with q hq
  unfold actualQExpression
  rw [hq,←evaluationChart_symm]
  exact (evaluationChart 0).right_inv (by rw [evaluationChart_target]; trivial)

/-- Canonical q-disc holomorphy and local ramification order for the exact
compact modular j map, over the full actual cusp-end type. -/
theorem actual_q_germ (c : End 3) : AnalyticAt ℂ (actualQExpression c) 0 ∧
    meromorphicOrderAt (actualQExpression c) 0=(qOrder c : ℤ) := by
  refine ⟨(qGerm_analytic c).congr (actualQExpression_eq c).symm,?_⟩
  rw [meromorphicOrderAt_congr ((actualQExpression_eq c).filter_mono nhdsWithin_le_nhds)]
  exact qGerm_order c

lemma named_q_orders : qOrder infinityEnd=1 ∧ qOrder zeroEnd=3 := by
  simp [qOrder,ends_distinct.symm]

end ActualThreeJQDiscGerms318
