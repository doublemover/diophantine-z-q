module
public import RotatedCuspOrbit318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open scoped MatrixGroups
namespace ActualThreeCuspOrbit318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The trace congruence at level three excludes the negative-unipotent
branch directly: three does not divide four. No high-level freeness theorem
or false inequality 5 <= 3 is used. -/
theorem upper_triangular_translation (g k:SL(2,ℤ))
    (hk:g*k*g⁻¹∈CongruenceSubgroup.Gamma1 3) (hc:k 1 0=0) :
    k=ModularGroup.T^(k 0 1) := by
  have hd:k 0 0*k 1 1=1 := by
    have := k.det_coe
    rwa [Matrix.det_fin_two,hc,mul_zero,sub_zero] at this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hd with ⟨ha,hd⟩ | ⟨ha,hd⟩
  · ext i j;fin_cases i <;>fin_cases j <;>
      simp [ha,hd,hc,ModularGroup.coe_T_zpow]
  · have ht := GammaOneFree318.trace_congruence 3 _ hk
    rw [RotatedStabilizer318.conjugate_trace,ha,hd] at ht
    norm_num at ht

theorem high_translation (g k:SL(2,ℤ))
    (hk:g*k*g⁻¹∈CongruenceSubgroup.Gamma1 3) (tau:UpperHalfPlane)
    (ht:1<tau.im) (hkt:1<(k•tau).im) :
    ∃n:ℤ,k=ModularGroup.T^n ∧ (RotatedWidths318.width 3 (by decide) g:ℤ)∣n := by
  have he:=upper_triangular_translation g k hk
    (RotatedStabilizer318.lower_left_zero_of_high k tau ht hkt)
  refine ⟨k 0 1,he,?_⟩
  exact (RotatedWidths318.period_iff 3 (by decide) g _).mp (he ▸ hk)

theorem rotated_orbit_iff_translation (g:SL(2,ℤ))
    (tau sigma:UpperHalfPlane) (ht:1<tau.im) (hs:1<sigma.im) :
    quotientMap 3 (g•tau)=quotientMap 3 (g•sigma) ↔
      ∃n:ℤ,(RotatedWidths318.width 3 (by decide) g:ℤ)∣n ∧ tau=ModularGroup.T^n•sigma := by
  constructor
  · intro he
    obtain ⟨delta,hd⟩:=MulAction.orbitRel_apply.mp (Quotient.exact he)
    obtain ⟨gamma,hgamma⟩:=delta.property
    have hact:gamma.val•(g•sigma)=g•tau := by
      change (delta.val:DerivativeCocycle318.G)•(g•sigma)=g•tau at hd
      rw [←hgamma] at hd
      exact hd
    let k:SL(2,ℤ):=g⁻¹*gamma.val*g
    have hk:g*k*g⁻¹∈CongruenceSubgroup.Gamma1 3 := by
      simpa only [k,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,one_mul,mul_one] using gamma.property
    have hkact:k•sigma=tau := by
      change (g⁻¹*gamma.val*g)•sigma=tau
      rw [mul_smul,mul_smul,hact,inv_smul_smul]
    obtain ⟨n,hn,hdiv⟩:=high_translation g k hk sigma hs (hkact ▸ ht)
    exact ⟨n,hdiv,hkact.symm.trans (congrArg (fun a:SL(2,ℤ)=>a•sigma) hn)⟩
  · rintro ⟨n,hdiv,htau⟩
    have hg:(g*ModularGroup.T^n*g⁻¹)∈CongruenceSubgroup.Gamma1 3 :=
      (RotatedWidths318.period_iff 3 (by decide) g n).mpr hdiv
    have he:g•tau=(g*ModularGroup.T^n*g⁻¹)•(g•sigma) := by
      rw [htau,mul_smul,mul_smul,inv_smul_smul]
    rw [he]
    exact FiniteCuspCoverage318.quotient_smul 3 ⟨_,hg⟩ _

/-- Exact q-width classification on the actual rotated high cusp region.
The width is constructed from the conjugated stabilizer and divides three. -/
theorem high_orbit_iff_q (g:SL(2,ℤ))
    (tau sigma:UpperHalfPlane) (ht:1<tau.im) (hs:1<sigma.im) :
    quotientMap 3 (g•tau)=quotientMap 3 (g•sigma) ↔
      Periodic.qParam (RotatedWidths318.width 3 (by decide) g:ℝ) tau=
        Periodic.qParam (RotatedWidths318.width 3 (by decide) g:ℝ) sigma := by
  let w:ℕ:=RotatedWidths318.width 3 (by decide) g
  have hw:(w:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (RotatedWidths318.width_positive 3 (by decide) g))
  rw [rotated_orbit_iff_translation g tau sigma ht hs,RotatedCuspOrbit318.q_eq_iff (w:ℝ) hw]
  constructor
  · rintro ⟨n,⟨m,hm⟩,he⟩
    refine ⟨m,?_⟩
    rw [he,ModularGroup.coe_T_zpow_smul_eq,hm]
    push_cast
    ring
  · rintro ⟨m,hm⟩
    refine ⟨(w:ℤ)*m,⟨m,rfl⟩,?_⟩
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq]
    push_cast
    simpa only [mul_comm,Complex.ofReal_natCast] using hm

end ActualThreeCuspOrbit318
