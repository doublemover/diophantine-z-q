module
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace FiniteReducedComplexAlgebra318
variable (A : Type*) [CommRing A] [Algebra ℂ A]
  [Module.Finite ℂ A] [IsReduced A]
/-- A finite reduced complex algebra is genuinely etale: the actual
Artinian quotient decomposition gives finite separable residue fields. -/
theorem etale : Algebra.Etale ℂ A := by
  letI : IsArtinianRing A := isArtinian_of_tower ℂ inferInstance
  letI (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  apply (Algebra.Etale.iff_exists_algEquiv_prod ℂ A).mpr
  exact ⟨MaximalSpectrum A, inferInstance, (fun m => A ⧸ m.asIdeal),
    inferInstance, inferInstance, (IsArtinianRing.equivPi A).restrictScalars ℂ,
    fun _ => ⟨inferInstance, inferInstance⟩⟩
/-- The actual algebra, not merely its radical quotient, splits over C
with one factor for EVERY prime. No numerical cardinality is presumed. -/
@[expose] def split : A ≃ₐ[ℂ] (PrimeSpectrum A → ℂ) := by
  letI := etale A
  exact Algebra.FormallyEtale.equivPiOfIsSepClosed ℂ A
end FiniteReducedComplexAlgebra318
