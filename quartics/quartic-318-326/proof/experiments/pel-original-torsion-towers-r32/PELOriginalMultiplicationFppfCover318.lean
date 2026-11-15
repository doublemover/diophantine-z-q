module
public import PELOriginalMultiplicationLocalDivision318
public import RelativeFppfLineSheaf318
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public section
noncomputable section
namespace PELOriginalMultiplicationFppfCover318
open AlgebraicGeometry CategoryTheory
open PELOriginalSchemePointGroup318 PELOriginalMultiplicationLocalDivision318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)
variable {T : Scheme} (ρ : T ⟶ Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)

/-- The actual single finite division cover belongs to the big relative
fppf topology. This uses the same native precoverage producer as the
original relative-line construction, without importing its bounded
Cartier presentation or supplying a fictitious local root. -/
lemma covering (hn : n≠0) :
    Sieve.ofArrows (fun _ : PUnit => Over.mk (coverBase τ hτ n ρ p))
      (fun _ => Over.homMk (projection τ hτ n ρ p) rfl) ∈
      RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)) (Over.mk ρ) := by
  letI := smooth_projection τ hτ n ρ p hn
  letI := surjective_projection τ hτ n ρ p hn
  rw [RelativeFppfLineSheaf318.topology,GrothendieckTopology.mem_over_iff,Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  apply (Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
  constructor
  · intro x
    obtain ⟨y,hy⟩ := (projection τ hτ n ρ p).surjective x
    exact ⟨PUnit.unit,y,hy⟩
  · intro i
    exact ⟨inferInstance,inferInstance⟩

/-- Every test point is n-divisible after this specific fppf cover,
with the genuine original group operation and the literal covering arrow. -/
lemma local_root (hn : n≠0) :
    (Sieve.ofArrows (fun _ : PUnit => Over.mk (coverBase τ hτ n ρ p))
      (fun _ => Over.homMk (projection τ hτ n ρ p) rfl) ∈
      RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)) (Over.mk ρ)) ∧
    n • root τ hτ n ρ p=pull τ hτ ρ (projection τ hτ n ρ p) rfl p :=
  ⟨covering τ hτ n ρ p hn,root_equation τ hτ n ρ p⟩
end PELOriginalMultiplicationFppfCover318
