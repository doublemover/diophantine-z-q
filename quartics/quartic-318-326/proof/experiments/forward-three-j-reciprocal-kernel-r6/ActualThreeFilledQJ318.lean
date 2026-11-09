module
public import ActualThreeCuspCompact318
public import FilledJInfinity318
public import ActualThreeCuspJ318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 ActualThreeCuspOverlap318 ActualThreeCuspFilling318 QuotientJ318
open scoped MatrixGroups
namespace ActualThreeFilledQJ318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def natWidth (c:End 3) : ℕ :=
  RotatedWidths318.width 3 (by decide) (representative 3 c)

theorem natWidth_pos (c:End 3) : 0<natWidth c :=
  RotatedWidths318.width_positive 3 (by decide) _

theorem width_eq_cast (c:End 3) : width c=(natWidth c:ℝ) := rfl

theorem qParam_pow (w:ℕ) (hw:0<w) (tau:UpperHalfPlane) :
    (Periodic.qParam (w:ℝ) tau)^w=Periodic.qParam 1 tau := by
  simp only [Periodic.qParam,←Complex.exp_nat_mul]
  congr 1
  have hwc:(w:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hw)
  push_cast
  field_simp

theorem j_rotated (g:SL(2,ℤ)) (tau:UpperHalfPlane) :
    jMap 3 (quotientMap 3 (g•tau))=ActualQJ318.jInvariant tau := by
  rw [jMap_projection,ModularGroup.sl_moeb]
  exact ActualJInvariant318.modular_invariant _ ⟨g,rfl⟩ tau

/-- The actual j expression at every selected cusp has its actual constructed
width as pole exponent. No q-expansion model is assumed. -/
theorem j_oldMap (c:End 3) (q:punctured (width c) 2) :
    jMap 3 (oldMap ⟨c,q⟩)=
      ActualQJ318.G (q.val^natWidth c)/(q.val^natWidth c) := by
  obtain ⟨tau,htau⟩:=qMap_surjective (width c) 2 (width_pos c) (by norm_num) q
  subst q
  have hold:oldMap ⟨c,qMap (width c) 2 (width_pos c) tau⟩=
      quotientMap 3 (representative 3 c•tau.val) := by
    change ((ActualThreeCuspHomeomorph318.cuspHomeomorph (representative 3 c)).symm
      (qMap (ActualThreeCuspHomeomorph318.wReal (representative 3 c)) 2
        (ActualThreeCuspHomeomorph318.wReal_pos (representative 3 c)) tau)).val=_
    rw [←ActualThreeCuspHomeomorph318.cuspHomeomorph_projection (representative 3 c) tau,
      Homeomorph.symm_apply_apply]
    rfl
  rw [hold,j_rotated]
  have hpow:(qMap (width c) 2 (width_pos c) tau).val^natWidth c=
      Periodic.qParam 1 tau := qParam_pow _ (natWidth_pos c) tau
  rw [hpow,ActualQJ318.G_qParam]
  field_simp [Periodic.qParam_ne_zero (tau:ℂ)]

/-- The normalized power map tends to zero, so actual j escapes every bound
near each added cusp, uniformly in a small local disc. -/
theorem small_parameter_large_j (c:End 3) (M:ℝ) :
    ∃epsilon:ℝ,0<epsilon ∧ ∀q:ℂ,‖q‖<epsilon→q≠0→
      M<‖ActualQJ318.G (q^natWidth c)/(q^natWidth c)‖ := by
  obtain ⟨delta,hdelta,hd⟩:=CuspSeparation318.small_parameter_large_j M
  have hpow:ContinuousAt (fun q:ℂ=>q^natWidth c) 0:=continuousAt_id.pow _
  have hz:(0:ℂ)^natWidth c=0:=zero_pow (Nat.ne_of_gt (natWidth_pos c))
  have he:∀ᶠq in 𝓝 (0:ℂ),‖q^natWidth c‖<delta := by
    have hnorm:Tendsto (fun q:ℂ=>‖q^natWidth c‖) (𝓝 0) (𝓝 0) := by
      have hn:=hpow.norm
      change Tendsto _ _ (𝓝 ‖(0:ℂ)^natWidth c‖) at hn
      rwa [hz,norm_zero] at hn
    exact hnorm.eventually (eventually_lt_nhds hdelta)
  obtain ⟨epsilon,hepsilon,hball⟩:=Metric.mem_nhds_iff.mp he
  refine ⟨epsilon,hepsilon,?_⟩
  intro q hq hne
  exact hd _ (hball (by simpa using hq)) (pow_ne_zero _ hne)

end ActualThreeFilledQJ318
