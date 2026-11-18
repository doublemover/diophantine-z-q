module
public import CuspOrbit318
public import Mathlib.Analysis.Normed.Group.Bounded
public section
noncomputable section
namespace LargeJActualOrbit318
open UpperHalfPlane ActualQJ318 Function
open scoped MatrixGroups Modular

theorem invariant (g : SL(2,ℤ)) (z : UpperHalfPlane) :
    jInvariant (g•z)=jInvariant z := by
  rw [ModularGroup.sl_moeb g]
  exact ActualJInvariant318.modular_invariant _ ⟨g,rfl⟩ z

/-- Instead of assuming global injectivity of modular j on X(1), prove the
needed orbit separation in a whole punctured neighborhood of infinity. The
genuine j is bounded on a truncated full fundamental domain. On its
complement the already constructed reciprocal-j inverse recovers q. -/
theorem one_orbit_above : ∃B:ℝ, ∀z w:UpperHalfPlane,
    B<‖jInvariant z‖ → jInvariant z=jInvariant w → ∃g:SL(2,ℤ),g•z=w := by
  obtain ⟨A,_,hA⟩ := CuspOrbit318.exists_high_recovery
  obtain ⟨B,hB⟩ := (ModularGroup.isCompact_truncatedFundamentalDomain A).exists_bound_of_continuousOn
    QuotientJ318.j_holomorphic.continuous.continuousOn
  refine ⟨B,?_⟩
  intro z w hz hj
  obtain ⟨s,hs⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨t,ht⟩ := ModularGroup.exists_smul_mem_fd w
  have hh {a : UpperHalfPlane} (ha : a∈ModularGroup.fd) (hb : B<‖jInvariant a‖) : A<a.im := by
    by_contra h
    exact hb.not_ge (hB a ⟨ha,le_of_not_gt h⟩)
  have hsz := hh hs (by rwa [invariant])
  have htw := hh ht (by rwa [invariant,←hj])
  have hq : Periodic.qParam 1 (s•z:UpperHalfPlane)=Periodic.qParam 1 (t•w:UpperHalfPlane) := by
    rw [←hA _ hsz,←hA _ htw,invariant,invariant,hj]
  obtain ⟨n,hn⟩ := CuspOrbit318.q_eq_translation _ _ hq
  have H : ModularGroup.T^n•(t•w)=s•z := by rw [modular_T_zpow_smul,hn]
  refine ⟨(ModularGroup.T^n*t)⁻¹*s,?_⟩
  rw [mul_smul,←H,←mul_smul,inv_smul_smul]
end LargeJActualOrbit318
