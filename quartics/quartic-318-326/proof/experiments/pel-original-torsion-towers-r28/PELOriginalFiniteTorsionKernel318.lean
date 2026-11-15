module
public import PELOriginalKernelComplexCardinality318
public import PELOriginalProperSmoothGroup318
public import FiniteComplexPointsScheme318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace PELOriginalFiniteTorsionKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalTorsionKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The original candidate is separated as an absolute scheme, using
its genuine proper complex structure map and the affine complex base. -/
lemma separated : (candidate τ hτ).IsSeparated := by
  refine ⟨?_⟩
  have h : IsSeparated (π τ hτ≫terminal.from (Spec (CommRingCat.of ℂ))) := inferInstance
  simpa only [terminal.comp_from] using h

lemma closed_inclusion (n : ℤ) : IsClosedImmersion (inclusion τ hτ n) := by
  letI := separated τ hτ
  exact inferInstanceAs (IsClosedImmersion
    (equalizer.ι (PELOriginalIntegerMultiplication318.multiplication τ hτ n)
      (PELOriginalSchemeGroupUnitInverse318.constantZero τ hτ)))
lemma proper (n : ℤ) : IsProper (structureMap τ hτ n) := by
  letI := closed_inclusion τ hτ n
  unfold structureMap
  infer_instance

/-- The ACTUAL scheme-theoretic kernel of multiplication by a positive
integer is finite over C. This is not the reduced finite zero locus: the
same categorical equalizer and all of its infinitesimal structure remain. -/
lemma finite (n : ℕ) (hn : 0<n) : IsFinite (structureMap τ hτ (n : ℤ)) := by
  letI := proper τ hτ (n : ℤ)
  letI : Finite (FiniteComplexPointsScheme318.Points (structureMap τ hτ (n : ℤ))) :=
    PELOriginalKernelComplexCardinality318.finite τ hτ n hn
  exact FiniteComplexPointsScheme318.finite_morphism (structureMap τ hτ (n : ℤ))

lemma finite_underlying (n : ℕ) (hn : 0<n) : Finite (kernel τ hτ (n : ℤ)) := by
  letI := proper τ hτ (n : ℤ)
  letI : Finite (FiniteComplexPointsScheme318.Points (structureMap τ hτ (n : ℤ))) :=
    PELOriginalKernelComplexCardinality318.finite τ hτ n hn
  exact FiniteComplexPointsScheme318.finite_space (structureMap τ hτ (n : ℤ))
end PELOriginalFiniteTorsionKernel318
