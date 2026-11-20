module
public import ActualJFinite318
public import ActualJImmersion318
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public section
noncomputable section

namespace SelectedJOneCover318
open Function Filter Topology Set Metric UpperHalfPlane unitInterval
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318 QuotientJ318
open OpenJLocalComparison318

/-- The open unit disk at 1 contains neither elliptic value. In particular
0 is excluded even though it lies on the boundary of the disk. -/
private theorem avoids (z : ℂ) (hz : z ∈ ball (1 : ℂ) 1) :
    z ≠ 0 ∧ z ≠ 1728 := by
  constructor
  · intro h
    subst z
    simpa only [mem_ball, dist_zero_left, norm_one, lt_self_iff_false] using hz
  · intro h
    subst z
    have hbad : ¬ ((1728 : ℂ) ∈ ball (1 : ℂ) 1) := by
      rw [mem_ball, dist_eq_norm, show (1728 : ℂ)-1 = (1727 : ℝ) by norm_num,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
      norm_num
    exact hbad hz

/-- The actual analytic orbit quotient's j-map, restricted to the open
unit disk at 1, is a covering. No assumed covering, no algebraic model. -/
theorem covering (N : ℕ) (hN : 5 ≤ N) :
    IsCoveringMapOn (jMap N) (ball (1 : ℂ) 1) := by
  letI := GammaOneAtlas318.quotient_hausdorff N
  apply (ActualJProper318.proper N hN).isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun z _ => ActualJFinite318.finite_fiber N hN z)
  apply IsLocalHomeomorphOn.mk
  intro q hq
  obtain ⟨tau,rfl⟩ := GammaOneAtlas318.quotient_surjective N q
  have hreg : OpenJComplexEvaluation318.Admissible tau :=
    avoids _ (by simpa only [mem_preimage, jMap_projection] using hq)
  let qp := GammaOneAtlas318.quotient_localHomeomorph N hN
  let co := UpperHalfPlane.isOpenEmbedding_coe.isLocalHomeomorph
  let D := (j_analyticAt tau).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (ActualJImmersion318.deriv_j_ne_zero tau hreg)
  let e := (qp.localInverseAt tau).trans ((co.localInverseAt tau).symm.trans
    (D.toOpenPartialHomeomorph j))
  refine ⟨e, ?_, ?_⟩
  · change _ ∈ (qp.localInverseAt tau).source ∧
      qp.localInverseAt tau (quotientMap N tau) ∈ ((co.localInverseAt tau).symm.trans
        (D.toOpenPartialHomeomorph j)).source
    refine ⟨qp.apply_self_mem_localInverseAt_source, ?_⟩
    rw [qp.localInverseAt_apply_self]
    refine ⟨co.self_mem_localInverseAt_target, ?_⟩
    rw [co.localInverseAt_symm]
    exact D.mem_toOpenPartialHomeomorph_source
  · intro y hy
    have hy₁ : y ∈ (qp.localInverseAt tau).source := hy.1
    change jMap N y = j ((co.localInverseAt tau).symm (qp.localInverseAt tau y))
    rw [co.localInverseAt_symm]
    have hproj : quotientMap N (qp.localInverseAt tau y) = y :=
      qp.apply_localInverseAt_of_mem hy₁
    calc
      jMap N y = jMap N (quotientMap N (qp.localInverseAt tau y)) :=
        congrArg (jMap N) hproj.symm
      _ = j ((qp.localInverseAt tau y : UpperHalfPlane) : ℂ) := by
        simp only [jMap_projection, j, UpperHalfPlane.ofComplex_apply]

private abbrev Disk := ↥(ball (0 : ℂ) 1)
private def center : Disk := ⟨0, mem_ball_self (by norm_num)⟩

/-- Radial lifting uses the entire open disk, not a germ or a smaller
closed disk. It also fixes the originally chosen center of the sheet. -/
private def radial : C(unitInterval × Disk, Disk) where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : ℂ), by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (unitInterval.nonneg p.1)]
    calc
      (p.1 : ℝ) * ‖(p.2 : ℂ)‖ ≤ ‖(p.2 : ℂ)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (unitInterval.le_one p.1)
      _ < 1 := by simpa only [mem_ball, dist_zero_right] using p.2.property⟩
  continuous_toFun := ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private theorem liftDisk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp : IsCoveringMap p) (q : C(Disk,Y)) (a : X)
    (ha : p a = q center) : ∃ F : C(Disk,X), F center = a ∧ p ∘ F = q := by
  let H := q.comp radial
  let f := ContinuousMap.const Disk a
  have hzero (z : Disk) : H (0,z) = p (f z) := by
    change q (radial (0,z)) = p a
    rw [ha]
    apply congrArg q
    apply Subtype.ext
    change ((0 : unitInterval) : ℝ) • (z : ℂ) = 0
    simp
  let W := hp.liftHomotopy H f hzero
  have hw := hp.liftHomotopy_lifts H f hzero
  let path : C(unitInterval,X) := W.comp
    ((ContinuousMap.id unitInterval).prodMk (ContinuousMap.const unitInterval center))
  have hpath : p ∘ path = p ∘ (fun _ : unitInterval => a) := by
    funext t
    change p (W (t,center)) = p a
    rw [show p (W (t,center)) = H (t,center) from congrFun hw (t,center)]
    change q (radial (t,center)) = p a
    rw [ha]
    apply congrArg q
    apply Subtype.ext
    change (t : ℝ) • (0 : ℂ) = 0
    simp
  have hap : path 0 = a := hp.liftHomotopy_zero H f hzero center
  have he := hp.eq_of_comp_eq path.continuous continuous_const hpath 0 hap
  refine ⟨W.comp ((ContinuousMap.const Disk (1 : unitInterval)).prodMk
    (ContinuousMap.id Disk)), congrFun he 1, ?_⟩
  funext z
  change p (W (1,z)) = q z
  rw [show p (W (1,z)) = H (1,z) from congrFun hw (1,z)]
  change q (radial (1,z)) = q z
  apply congrArg q
  apply Subtype.ext
  change ((1 : unitInterval) : ℝ) • (z : ℂ) = (z : ℂ)
  simp

/-- The actual inverse sheet of the level-N analytic quotient through the
given j=1 point; the inverse coordinate is precisely z = j-1. -/
theorem disk_section (N : ℕ) (hN : 5 ≤ N) (q : Base (image N))
    (hq : jMap N q = 1) :
    ∃ F : C(↥(ball (0 : ℂ) 1), Base (image N)),
      F ⟨0,mem_ball_self (by norm_num)⟩ = q ∧ ∀ z, jMap N (F z) = 1+(z : ℂ) := by
  let T := ball (1 : ℂ) 1
  let a : ↥((jMap N) ⁻¹' T) := ⟨q, by
    change jMap N q ∈ T
    rw [hq]
    exact mem_ball_self (by norm_num)⟩
  let addOne : C(Disk, T) :=
    ⟨fun z => ⟨1+(z : ℂ), by
      have hz := z.property
      simpa only [T, mem_ball, dist_eq_norm, sub_zero, add_sub_cancel_left] using hz⟩,
      Continuous.subtype_mk (continuous_const.add continuous_subtype_val) _⟩
  have ha : T.restrictPreimage (jMap N) a = addOne center := by
    apply Subtype.ext
    change jMap N q = 1+0
    simpa only [add_zero] using hq
  obtain ⟨F,hF,hsec⟩ := liftDisk (covering N hN).isCoveringMap_restrictPreimage addOne a ha
  refine ⟨⟨fun z => (F z).val, continuous_subtype_val.comp F.continuous⟩, ?_, ?_⟩
  · exact congrArg Subtype.val hF
  · intro z
    exact congrArg Subtype.val (congrFun hsec z)

/-- First pin the analytic inverse of j−1 at the actual selected period.
Equality of right inverses is used only as a germ, not to choose a new
sheet of the quotient. -/
private theorem inverse_germ {f g : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hn : deriv f x ≠ 0)
    (hg : Tendsto g (𝓝 (f x)) (𝓝 x))
    (hfg : ∀ᶠ z in 𝓝 (f x), f (g z) = z) : AnalyticAt ℂ g (f x) := by
  let r := hf.hasStrictDerivAt.localInverse f (deriv f x) x hn
  have hl : ∀ᶠ y in 𝓝 x, r (f y) = y :=
    hf.hasStrictDerivAt.eventually_left_inverse hn
  have he : r =ᶠ[𝓝 (f x)] g := by
    filter_upwards [hg.eventually hl,hfg] with z hz hz'
    rwa [hz'] at hz
  exact (hf.analyticAt_localInverse hn).congr he

/-- The lifted sheet has a holomorphic injective period coordinate over
the entire open unit disk. Its period at zero lies over the given q,
and the branch is tied to the same q by the literal orbit projection. -/
theorem holomorphic_disk_section (N : ℕ) (hN : 5 ≤ N) (q : Base (image N))
    (hq : jMap N q = 1) :
    ∃ T : C(↥(ball (0 : ℂ) 1), UpperHalfPlane), ∃ F : ℂ → ℂ,
      quotientMap N (T ⟨0,mem_ball_self (by norm_num)⟩) = q ∧
      (∀ z, F (z : ℂ) = (T z : ℂ)) ∧
      (∀ z, ActualQJ318.jInvariant (T z) = 1+(z : ℂ)) ∧
      AnalyticOnNhd ℂ F (ball 0 1) ∧
      InjOn (fun z : ↥(ball (0 : ℂ) 1) => quotientMap N (T z)) univ := by
  obtain ⟨S,hS,hj⟩ := disk_section N hN q hq
  obtain ⟨tau,htau⟩ := GammaOneAtlas318.quotient_surjective N q
  obtain ⟨T,hT,hproj⟩ := liftDisk (GammaOneAtlas318.quotient_covering N hN).isCoveringMap
    S tau (htau.trans hS.symm)
  classical
  let F : ℂ → ℂ := fun z => if hz : z ∈ ball (0 : ℂ) 1 then (T ⟨z,hz⟩ : ℂ) else 0
  have hF (z : Disk) : F (z : ℂ) = (T z : ℂ) := dif_pos z.property
  have hjT (z : Disk) : ActualQJ318.jInvariant (T z) = 1+(z : ℂ) := by
    have h := congrFun hproj z
    change quotientMap N (T z) = S z at h
    simpa only [← h,jMap_projection] using hj z
  have hc : ContinuousOn F (ball 0 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (ball (0 : ℂ) 1).domRestrict F = fun z : Disk => (T z : ℂ) := funext hF
    rw [he]
    exact UpperHalfPlane.continuous_coe.comp T.continuous
  let j₀ : ℂ → ℂ := fun w => j w - 1
  have hr (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : j₀ (F z) = z := by
    rw [show F z = (T ⟨z,hz⟩ : ℂ) from hF ⟨z,hz⟩]
    change j (T ⟨z,hz⟩ : ℂ)-1 = z
    simp only [j,UpperHalfPlane.ofComplex_apply,hjT,add_sub_cancel_left]
  refine ⟨T,F,?_,hF,hjT,?_,?_⟩
  · exact (congrArg (quotientMap N) hT).trans htau
  · intro z hz
    let uz := T ⟨z,hz⟩
    have huz : F z = (uz : ℂ) := hF ⟨z,hz⟩
    have hreg : OpenJComplexEvaluation318.Admissible uz := by
      apply avoids
      have hshift : (1+z : ℂ) ∈ ball 1 1 := by
        simpa only [mem_ball,dist_eq_norm,sub_zero,add_sub_cancel_left] using hz
      simpa only [uz,hjT] using hshift
    have hFz : j₀ (uz : ℂ) = z := by simpa only [← huz] using hr z hz
    have hder : deriv j₀ (uz : ℂ) = deriv j (uz : ℂ) :=
      ((j_analyticAt uz).differentiableAt.hasDerivAt.sub_const (1 : ℂ)).deriv
    have hg : Tendsto F (𝓝 (j₀ (uz : ℂ))) (𝓝 (uz : ℂ)) := by
      rw [hFz,← huz]
      exact ((hc z hz).continuousAt (isOpen_ball.mem_nhds hz)).tendsto
    have hfg : ∀ᶠ z' in 𝓝 (j₀ (uz : ℂ)), j₀ (F z') = z' := by
      rw [hFz]
      exact (isOpen_ball.mem_nhds hz).mono (fun z' hz' => hr z' hz')
    have hn : deriv j₀ (uz : ℂ) ≠ 0 := by
      rw [hder]
      exact ActualJImmersion318.deriv_j_ne_zero uz hreg
    have h := inverse_germ ((j_analyticAt uz).sub analyticAt_const) hn hg hfg
    rwa [hFz] at h
  · intro a _ b _ hab
    apply Subtype.ext
    have h := congrArg (jMap N) hab
    simp only [jMap_projection,hjT] at h
    exact add_left_cancel h

end SelectedJOneCover318
#print axioms SelectedJOneCover318.covering
#print axioms SelectedJOneCover318.disk_section
#print axioms SelectedJOneCover318.holomorphic_disk_section
