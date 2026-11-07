module
public import FiniteCuspCoverage318
public import Mathlib.Analysis.Complex.Periodic
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open scoped MatrixGroups
namespace RotatedCuspOrbit318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem q_eq_iff (w:ℝ) (hw:w≠0) (tau sigma:UpperHalfPlane) :
    Periodic.qParam w tau=Periodic.qParam w sigma ↔
      ∃m:ℤ,(tau:ℂ)=(sigma:ℂ)+(m:ℂ)*w := by
  constructor
  · intro he
    obtain ⟨m,hm⟩:=Periodic.qParam_left_inv_mod_period hw (tau:ℂ)
    obtain ⟨n,hn⟩:=Periodic.qParam_left_inv_mod_period hw (sigma:ℂ)
    rw [he] at hm
    refine ⟨n-m,?_⟩
    push_cast
    linear_combination hn-hm
  · rintro ⟨m,he⟩
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨m,?_⟩
    rw [he]
    have hwC:(w:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hw
    field_simp

theorem rotated_orbit_iff_translation (N:ℕ) (hN:5≤N) (g:SL(2,ℤ))
    (tau sigma:UpperHalfPlane) (ht:1<tau.im) (hs:1<sigma.im) :
    quotientMap N (g•tau)=quotientMap N (g•sigma) ↔
      ∃n:ℤ,(RotatedWidths318.width N (by omega) g:ℤ)∣n ∧ tau=ModularGroup.T^n•sigma := by
  constructor
  · intro he
    obtain ⟨delta,hd⟩:=MulAction.orbitRel_apply.mp (Quotient.exact he)
    obtain ⟨gamma,hgamma⟩:=delta.property
    have hact:gamma.val•(g•sigma)=g•tau := by
      change (delta.val:DerivativeCocycle318.G)•(g•sigma)=g•tau at hd
      rw [←hgamma] at hd
      exact hd
    let k:SL(2,ℤ):=g⁻¹*gamma.val*g
    have hk:g*k*g⁻¹∈CongruenceSubgroup.Gamma1 N := by
      simpa only [k,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,one_mul,mul_one] using gamma.property
    have hkact:k•sigma=tau := by
      change (g⁻¹*gamma.val*g)•sigma=tau
      rw [mul_smul,mul_smul,hact,inv_smul_smul]
    obtain ⟨n,hn,hdiv⟩:=RotatedStabilizer318.high_translation N hN g k hk sigma hs (hkact ▸ ht)
    exact ⟨n,hdiv,hkact.symm.trans (congrArg (fun a:SL(2,ℤ)=>a•sigma) hn)⟩
  · rintro ⟨n,hdiv,htau⟩
    have hg:(g*ModularGroup.T^n*g⁻¹)∈CongruenceSubgroup.Gamma1 N :=
      (RotatedWidths318.period_iff N (by omega) g n).mpr hdiv
    have he:g•tau=(g*ModularGroup.T^n*g⁻¹)•(g•sigma) := by
      rw [htau,mul_smul,mul_smul,inv_smul_smul]
    rw [he]
    exact FiniteCuspCoverage318.quotient_smul N ⟨_,hg⟩ _

/-- Exact q-width classification on the actual rotated high cusp region.
The width is constructed from the conjugated stabilizer and divides N. -/
theorem high_orbit_iff_q (N:ℕ) (hN:5≤N) (g:SL(2,ℤ))
    (tau sigma:UpperHalfPlane) (ht:1<tau.im) (hs:1<sigma.im) :
    quotientMap N (g•tau)=quotientMap N (g•sigma) ↔
      Periodic.qParam (RotatedWidths318.width N (by omega) g:ℝ) tau=
        Periodic.qParam (RotatedWidths318.width N (by omega) g:ℝ) sigma := by
  let w:ℕ:=RotatedWidths318.width N (by omega) g
  have hw:(w:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (RotatedWidths318.width_positive N (by omega) g))
  rw [rotated_orbit_iff_translation N hN g tau sigma ht hs,q_eq_iff (w:ℝ) hw]
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

end RotatedCuspOrbit318
