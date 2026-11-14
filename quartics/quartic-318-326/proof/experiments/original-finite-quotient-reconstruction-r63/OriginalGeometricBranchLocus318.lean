module
public import NormalClosureGeometricPoints318
public section
noncomputable section
namespace OriginalGeometricBranchLocus318
open AlgebraicGeometry CategoryTheory
open OriginalNormalClosureGalois318 NormalClosureGeometricPoints318
variable {L : Type} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- Full stabilizers of all ACTUAL geometric points of the original affine
normal closure, with the literal original coordinate and labeled flips. -/
@[expose] def PointBranchLocus
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Order L →+* F),
    ((∀ k, coordinate L p ≠ contactValue L p k) ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, point L p ≫ schemeMap L σ = point L p ↔ σ = 1) ∨
    ∃ k : Fin 4, coordinate L p = contactValue L p k ∧
      ∀ σ : OriginalNormalClosureGalois318.Group L, point L p ≫ schemeMap L σ = point L p ↔
        σ = 1 ∨ labels σ = FourBinaryCharacters318.flip k

/-- Actual geometric-point stabilizers supply the WHOLE original ideal
inertia locus. The geometric residue embedding is injective and its kernel
is proved to be the same original prime before applying the stabilizer law. -/
theorem full_inertia
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (h : PointBranchLocus labels) : OriginalFullInertiaReconstruction318.BranchLocus labels := by
  intro q hq P hP hc
  letI := hP
  let p := geometricPoint L P
  have hk : RingHom.ker p = P := geometricPoint_kernel L P
  rcases h (AlgebraicClosure P.ResidueField) p with hu | ⟨k,he,hs⟩
  · refine Or.inl ⟨?_,?_⟩
    · intro σ
      exact (scheme_fixed_iff p P hk σ).symm.trans (hu.2 σ)
    · intro k ha
      exact hu.1 k ((contact_iff p P hk q hq hc k).mp ha)
  · refine Or.inr ⟨k,(contact_iff p P hk q hq hc k).mpr he,?_⟩
    intro σ
    exact (scheme_fixed_iff p P hk σ).symm.trans (hs σ)
end OriginalGeometricBranchLocus318
