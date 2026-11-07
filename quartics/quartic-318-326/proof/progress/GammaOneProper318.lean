module
public import GammaOneFiber318
public import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous
public import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
public section
noncomputable section
open UpperHalfPlane DerivativeCocycle318 GammaOneFiber318
open scoped MatrixGroups
namespace GammaOneProper318
set_option maxHeartbeats 0

/-- The actual fine-level positive-matrix image acts properly discontinuously.
This is derived from the genuine integral modular-group action, not assumed. -/
instance properlyDiscontinuous (N:ℕ) : ProperlyDiscontinuousSMul (image N) UpperHalfPlane := by
  have hfull : ProperlyDiscontinuousSMul
      (Matrix.SpecialLinearGroup.mapGL (n:=Fin 2) (R:=ℤ) ℝ).range UpperHalfPlane := inferInstance
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hfull ⊢
  intro K L hK hL
  have hf := hfull hK hL
  have hpre := hf.preimage (f:=fun g:G=>(g:GL (Fin 2) ℝ)) Subtype.val_injective.injOn
  apply hpre.subset
  rintro g ⟨hg,hint⟩
  change (g:GL (Fin 2) ℝ)∈(Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range ∧ _
  refine ⟨?_,hint⟩
  obtain ⟨gamma,rfl⟩:=hg
  exact ⟨gamma.val,rfl⟩

/-- Freeness of the exact fine-level subgroup, in the standard action API. -/
instance cancelSMul (N:ℕ) [Fact (5≤N)] : IsCancelSMul (image N) UpperHalfPlane := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g z hz
  apply Subtype.ext
  exact image_fixed_eq_one N Fact.out g g.property z hz
end GammaOneProper318
