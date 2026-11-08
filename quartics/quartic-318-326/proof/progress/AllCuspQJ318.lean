module
public import AllCuspCompact318
public import FilledJInfinity318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 FiniteCuspEnds318 AllCuspOverlap318 AllCuspFilling318 QuotientJ318
open scoped MatrixGroups
namespace AllCuspQJ318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def natWidth (N:ℕ) (hN:5≤N) (c:End N) : ℕ :=
  RotatedWidths318.width N (by omega) (representative N c)

theorem natWidth_pos (N:ℕ) (hN:5≤N) (c:End N) : 0<natWidth N hN c :=
  RotatedWidths318.width_positive N (by omega) _

theorem width_eq_cast (N:ℕ) (hN:5≤N) (c:End N) : width N hN c=(natWidth N hN c:ℝ) := rfl

theorem qParam_pow (w:ℕ) (hw:0<w) (tau:UpperHalfPlane) :
    (Periodic.qParam (w:ℝ) tau)^w=Periodic.qParam 1 tau := by
  simp only [Periodic.qParam,←Complex.exp_nat_mul]
  congr 1
  have hwc:(w:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hw)
  push_cast
  field_simp

theorem j_rotated (N:ℕ) (g:SL(2,ℤ)) (tau:UpperHalfPlane) :
    jMap N (quotientMap N (g•tau))=ActualQJ318.jInvariant tau := by
  rw [jMap_projection,ModularGroup.sl_moeb]
  exact ActualJInvariant318.modular_invariant _ ⟨g,rfl⟩ tau

/-- The actual j expression at every selected cusp has its actual constructed
width as pole exponent. No q-expansion model is assumed. -/
theorem j_oldMap (N:ℕ) (hN:5≤N) (c:End N) (q:punctured (width N hN c) 2) :
    jMap N (oldMap N hN ⟨c,q⟩)=
      ActualQJ318.G (q.val^natWidth N hN c)/(q.val^natWidth N hN c) := by
  obtain ⟨tau,htau⟩:=qMap_surjective (width N hN c) 2 (width_pos N hN c) (by norm_num) q
  subst q
  have hold:oldMap N hN ⟨c,qMap (width N hN c) 2 (width_pos N hN c) tau⟩=
      quotientMap N (representative N c•tau.val) := by
    change ((RotatedHomeomorph318.cuspHomeomorph N hN (representative N c)).symm
      (qMap (RotatedHomeomorph318.wReal N hN (representative N c)) 2
        (RotatedHomeomorph318.wReal_pos N hN (representative N c)) tau)).val=_
    rw [←RotatedHomeomorph318.cuspHomeomorph_projection N hN (representative N c) tau,
      Homeomorph.symm_apply_apply]
    rfl
  rw [hold,j_rotated]
  have hpow:(qMap (width N hN c) 2 (width_pos N hN c) tau).val^natWidth N hN c=
      Periodic.qParam 1 tau := qParam_pow _ (natWidth_pos N hN c) tau
  rw [hpow,ActualQJ318.G_qParam]
  field_simp [Periodic.qParam_ne_zero (tau:ℂ)]

/-- The normalized power map tends to zero, so actual j escapes every bound
near each added cusp, uniformly in a small local disc. -/
theorem small_parameter_large_j (N:ℕ) (hN:5≤N) (c:End N) (M:ℝ) :
    ∃epsilon:ℝ,0<epsilon ∧ ∀q:ℂ,‖q‖<epsilon→q≠0→
      M<‖ActualQJ318.G (q^natWidth N hN c)/(q^natWidth N hN c)‖ := by
  obtain ⟨delta,hdelta,hd⟩:=CuspSeparation318.small_parameter_large_j M
  have hpow:ContinuousAt (fun q:ℂ=>q^natWidth N hN c) 0:=continuousAt_id.pow _
  have hz:(0:ℂ)^natWidth N hN c=0:=zero_pow (Nat.ne_of_gt (natWidth_pos N hN c))
  have he:∀ᶠq in 𝓝 (0:ℂ),‖q^natWidth N hN c‖<delta := by
    have hnorm:Tendsto (fun q:ℂ=>‖q^natWidth N hN c‖) (𝓝 0) (𝓝 0) := by
      have hn:=hpow.norm
      change Tendsto _ _ (𝓝 ‖(0:ℂ)^natWidth N hN c‖) at hn
      rwa [hz,norm_zero] at hn
    exact hnorm.eventually (eventually_lt_nhds hdelta)
  obtain ⟨epsilon,hepsilon,hball⟩:=Metric.mem_nhds_iff.mp he
  refine ⟨epsilon,hepsilon,?_⟩
  intro q hq hne
  exact hd _ (hball (by simpa using hq)) (pow_ne_zero _ hne)

end AllCuspQJ318
