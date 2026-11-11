module
public import PELOriginalKernelRelationMap318
public import ProperSelfRelationFinite318
public section
noncomputable section
namespace PELOriginalFiniteMultiplication318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalIntegerMultiplication318 PELOriginalTorsionKernelScheme318
open PELOriginalKernelRelationMap318
variable (τ : ℂ) (hτ : 0 < τ.im)
lemma proper (n : ℤ) : IsProper (multiplication τ hτ n) := by
  letI : IsProper (multiplication τ hτ n≫π τ hτ) := by
    rw [over_complex]
    infer_instance
  exact IsProper.of_comp (multiplication τ hτ n) (π τ hτ)

/-- The actual kernel-product relation map is surjective on ALL primes,
and its composite second projection is finite. Proper finite-fiber
descent therefore makes the full self-relation projection finite. -/
lemma finite_relation (n : ℕ) (hn : 0<n) :
    IsFinite (pullback.snd (multiplication τ hτ (n : ℤ)) (multiplication τ hτ (n : ℤ))) := by
  letI := proper τ hτ (n : ℤ)
  letI := PELOriginalFiniteTorsionKernel318.finite τ hτ n hn
  letI : IsFinite (forward τ hτ (n : ℤ)≫
      pullback.snd (multiplication τ hτ (n : ℤ)) (multiplication τ hτ (n : ℤ))) := by
    rw [forward_second]
    exact inferInstanceAs (IsFinite (pullback.snd (structureMap τ hτ (n : ℤ)) (π τ hτ)))
  exact ProperFiniteFiberDescent318.finite (forward τ hτ (n : ℤ))
    (pullback.snd _ _) (surjective τ hτ (n : ℤ))

/-- Multiplication by EVERY positive integer on the SAME constructed
original algebraic group is a genuine finite scheme morphism. The proof
uses the entire scheme-theoretic kernel and universal relation map;
no reduced-kernel or finite-closed-fiber surrogate is substituted. -/
lemma finite (n : ℕ) (hn : 0<n) : IsFinite (multiplication τ hτ (n : ℤ)) := by
  letI := proper τ hτ (n : ℤ)
  letI := finite_relation τ hτ n hn
  exact ProperSelfRelationFinite318.finite_of_self_pullback (multiplication τ hτ (n : ℤ))
end PELOriginalFiniteMultiplication318
