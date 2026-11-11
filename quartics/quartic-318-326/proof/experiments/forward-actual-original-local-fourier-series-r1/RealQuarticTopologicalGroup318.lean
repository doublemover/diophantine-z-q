module
public import RealQuarticGroup318
public section
noncomputable section
namespace RealQuarticTopologicalGroup318
open Set ReciprocalGroup318 RealQuarticGroup318 RealQuarticSumAnalytic318
set_option maxHeartbeats 2000000

lemma add_continuous {D : ℝ} (hD : 0<D) :
    Continuous (fun z : Oval D × Oval D => RealQuarticGroup318.add hD z.1 z.2) := by
  let f (z : Oval D × Oval D) : Fin 4 → ℝ := ![z.1.val.1,z.1.val.2,z.2.val.1,z.2.val.2]
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hc (i : Fin 4) (x : Fin 4 → ℝ) : AnalyticAt ℝ (fun y : Fin 4 → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R:=ℝ) i).analyticAt x
  have hU : Continuous (fun x : Fin 4 → ℝ => sumU D (x 0) (x 1) (x 2) (x 3)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (sumU_analytic hD (hc 0 x) (hc 1 x) (hc 2 x) (hc 3 x)).continuousAt
  have hV : Continuous (fun x : Fin 4 → ℝ => sumV D (x 0) (x 1) (x 2) (x 3)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (sumV_analytic hD (hc 0 x) (hc 1 x) (hc 2 x) (hc 3 x)).continuousAt
  apply continuous_induced_rng.mpr
  exact (hU.comp hf).prodMk (hV.comp hf)

lemma neg_continuous (D : ℝ) : Continuous (@RealQuarticGroup318.neg D) := by
  apply continuous_induced_rng.mpr
  exact (continuous_fst.comp continuous_subtype_val).neg.prodMk
    (continuous_snd.comp continuous_subtype_val)

/-- The group law is continuous in the original real subspace topology. -/
theorem topologicalGroup (D : ℝ) (hD : 0<D) :
    let := group D hD
    IsTopologicalAddGroup (Oval D) := by
  let := group D hD
  exact { continuous_add := add_continuous hD, continuous_neg := neg_continuous D }

/-- Compactness of the full real oval, for every positive real coefficient.
No compactification or group-topology transport is used. -/
theorem compactSpace (D : ℝ) (hD : 0<D) : CompactSpace (Oval D) := by
  apply isCompact_iff_compactSpace.mp
  have hclosed : IsClosed {p : ℝ × ℝ | p.2^2=1-D*p.1^4} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply (isCompact_closedBall (0:ℝ × ℝ) (1+RealQuarticOvalCover318.radius D)).of_isClosed_subset hclosed
  intro p hp
  obtain ⟨t,hu,hv⟩ := RealQuarticOvalCover318.oval_surjective hD p.1 p.2 hp
  have hc := RealQuarticOvalCover318.radius_positive hD
  have hub : |p.1|≤RealQuarticOvalCover318.radius D := by
    rw [←hu,RealQuarticOvalCover318.u,abs_mul,abs_of_pos hc]
    exact mul_le_of_le_one_right hc.le (Real.abs_sin_le_one t)
  have hvb : |p.2|≤1 := by
    apply (sq_le_one_iff_abs_le_one _).mp
    have hn : 0≤D*p.1^4 := mul_nonneg hD.le (by positivity)
    have he : p.2^2=1-D*p.1^4 := hp
    linarith
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
  simp only [Real.norm_eq_abs]
  constructor <;> linarith

end RealQuarticTopologicalGroup318
