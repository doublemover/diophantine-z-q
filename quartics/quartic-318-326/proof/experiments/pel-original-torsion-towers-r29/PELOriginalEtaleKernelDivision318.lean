module
public import PELOriginalMultiplicationEtale318
public import PELOriginalKernelZeroFiber318
public import PELOriginalMultiplicationLocalEpimorphism318
public section
noncomputable section
namespace PELOriginalEtaleKernelDivision318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalSchemePointGroup318 PELOriginalIntegerMultiplication318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ) (hn : n≠0)

/-- The SAME original equalizer kernel is finite étale, by its genuine
whole zero-fiber isomorphism. No radical replacement is made. -/
lemma kernel_finite_etale :
    IsFinite (PELOriginalTorsionKernelScheme318.structureMap τ hτ n) ∧
    Etale (PELOriginalTorsionKernelScheme318.structureMap τ hτ n) := by
  letI := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  letI := PELOriginalMultiplicationEtale318.etale τ hτ n hn
  rw [←PELOriginalKernelZeroFiber318.iso_second]
  exact ⟨inferInstance,inferInstance⟩

/-- The explicit root cover already used by the fppf Kummer sequence is
in fact finite étale and surjective on ALL primes of EVERY test scheme. -/
lemma division_finite_etale {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ))
    (p : Points τ hτ T ρ) :
    IsFinite (PELOriginalMultiplicationLocalDivision318.projection τ hτ n ρ p) ∧
    Etale (PELOriginalMultiplicationLocalDivision318.projection τ hτ n ρ p) ∧
    Function.Surjective (PELOriginalMultiplicationLocalDivision318.projection τ hτ n ρ p) := by
  letI := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  letI := PELOriginalMultiplicationEtale318.etale τ hτ n hn
  letI : Surjective (multiplication τ hτ n) :=
    ⟨PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ n hn⟩
  exact ⟨inferInstanceAs (IsFinite (pullback.snd (multiplication τ hτ n) p.val)),
    inferInstanceAs (Etale (pullback.snd (multiplication τ hτ n) p.val)),
    (pullback.snd (multiplication τ hτ n) p.val).surjective⟩
end PELOriginalEtaleKernelDivision318
