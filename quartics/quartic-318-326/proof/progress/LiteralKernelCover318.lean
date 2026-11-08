module
public import LiteralKernelCoordinateRing318
public section
noncomputable section
namespace LiteralKernelCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 500000
variable (N:ℕ)

/-- The actual zero section makes the whole kernel map surjective, even
when the base itself is empty. -/
lemma surjective : Surjective (LiteralKernelFiniteEtale318.structureMap N) := by
  constructor
  intro x
  refine ⟨LiteralKernelZeroSection318.toKernel N x,?_⟩
  change (LiteralKernelZeroSection318.toKernel N ≫ LiteralKernelFiniteEtale318.structureMap N) x=x
  rw [LiteralKernelFiniteEtale318.structureMap,LiteralKernelZeroSection318.toKernel_snd]
  rfl

/-- All properties refer to the same actual kernel projection. -/
theorem finite_etale_flat_surjective :
    IsFinite (LiteralKernelFiniteEtale318.structureMap N) ∧
    Etale (LiteralKernelFiniteEtale318.structureMap N) ∧
    Flat (LiteralKernelFiniteEtale318.structureMap N) ∧
    Surjective (LiteralKernelFiniteEtale318.structureMap N) := by
  obtain ⟨hf,he⟩:=LiteralKernelFiniteEtale318.finite_etale N
  haveI:=he
  exact ⟨hf,he,inferInstance,surjective N⟩
end LiteralKernelCover318
