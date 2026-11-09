module
public import RealQuarticOvalCover318
public import RealGuardCover318
public section
noncomputable section
namespace RealQuarticProductCover318
open Set RealQuarticAmbient318 RealQuarticOvalCover318
set_option maxHeartbeats 1000000

abbrev Angles := (Fin 8 × Fin 2) → ℝ

@[expose] def cover (t : Angles) : Ambient :=
  fun ⟨i,e,c⟩ => if c=0 then u (d e) (t (i,e)) else v (t (i,e))

lemma cover_mem (t : Angles) : cover t∈ovals := by
  intro i e
  simpa [cover] using oval_equation (lt_trans zero_lt_one (d_gt_one e)) (t (i,e))

/-- The explicit independent-angle map is globally analytic in the ordinary
normed coordinate spaces. It is not asserted to be a group homomorphism. -/
theorem cover_analytic : AnalyticOnNhd ℝ cover univ := by
  intro t _
  apply analyticAt_pi_iff.mpr
  rintro ⟨i,e,c⟩
  have hp : AnalyticAt ℝ (fun s : Angles => s (i,e)) t :=
    (ContinuousLinearMap.proj (R:=ℝ) (i,e)).analyticAt t
  by_cases hc : c=0
  · simpa only [cover,ite_eq_left hc,Function.comp_apply] using (u_analytic (d e) (t (i,e))).fun_comp (f:=fun s : Angles => s (i,e)) (x:=t) hp
  · simpa only [cover,ite_eq_right hc,Function.comp_apply] using (v_analytic (t (i,e))).fun_comp (f:=fun s : Angles => s (i,e)) (x:=t) hp

@[expose] def ovalCover (t : Angles) : ovals := ⟨cover t,cover_mem t⟩

theorem ovalCover_surjective : Function.Surjective ovalCover := by
  intro z
  have hex (i : Fin 8) (e : Fin 2) :
      ∃ t : ℝ, u (d e) t=z.val (i,e,0) ∧ v t=z.val (i,e,1) :=
    oval_surjective (lt_trans zero_lt_one (d_gt_one e)) _ _ (z.property i e)
  choose t ht using hex
  refine ⟨fun ⟨i,e⟩ => t i e,?_⟩
  apply Subtype.ext
  funext a
  rcases a with ⟨i,e,c⟩
  fin_cases c
  · simpa [ovalCover,cover] using (ht i e).1
  · simpa [ovalCover,cover] using (ht i e).2

theorem ovalCover_continuous : Continuous ovalCover :=
  continuous_induced_rng.mpr (continuousOn_univ.mp cover_analytic.continuousOn)

/-- Translating the independent-angle domain centers the actual analytic
surjection at the literal identity orbit point, with no branch selection left
as a hypothesis. This covers the full product, not a cyclic orbit component. -/
theorem centered_cover (n : Fin 4 → ℤ) :
    ∃ π : Angles → ovals, Function.Surjective π ∧
      AnalyticOnNhd ℝ (fun x => (π x).val) univ ∧ (π 0).val=orbit n 0 := by
  obtain ⟨t0,ht0⟩ := ovalCover_surjective ⟨orbit n 0,orbit_mem n 0⟩
  refine ⟨fun t => ovalCover (t+t0),?_,?_,?_⟩
  · intro z
    obtain ⟨t,ht⟩ := ovalCover_surjective z
    refine ⟨t-t0,?_⟩
    simpa only [sub_add_cancel] using ht
  · intro t _
    exact (cover_analytic (t+t0) (mem_univ _)).comp (f:=fun s : Angles => s+t0) (x:=t) (analyticAt_id.add analyticAt_const)
  · simpa only [zero_add] using congrArg Subtype.val ht0

/-- Actual simultaneous zero avoidance on the entire product of real source
ovals. Transferring this to a smaller closed orbit component remains separate. -/
theorem actual_guards_dense (n : Fin 4 → ℤ) (hn : ∀ j, n j≠0) :
    Dense {z : ovals | ∀ j : Fin 4, RealGuardAmbient318.guard j z.val≠0} := by
  obtain ⟨π,hs,ha,h0⟩ := centered_cover n
  exact RealGuardCover318.good_dense_of_analytic_cover n hn ovals π hs ha h0

end RealQuarticProductCover318
