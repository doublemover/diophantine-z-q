module
public import PELOriginalOrderLocalDivision318
public import RelativeFppfLineSheaf318
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public section
noncomputable section
namespace PELOriginalOrderFppfDivision318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalOrderIntegralNorm318
open PELOriginalSchemePointGroup318 PELOriginalOrderLocalDivision318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
variable {T : Scheme} (ρ : T ⟶ Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)

/-- The actual single finite division cover belongs to the big relative
fppf topology. This uses the same native precoverage producer as the
original relative-line construction, without importing its bounded
Cartier presentation or supplying a fictitious local root. -/
lemma covering (ha : norm a≠0) :
    Sieve.ofArrows (fun _ : PUnit => Over.mk (coverBase τ hτ a ρ p))
      (fun _ => Over.homMk (projection τ hτ a ρ p) rfl) ∈
      RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)) (Over.mk ρ) := by
  letI := smooth_projection τ hτ a ρ p ha
  letI := surjective_projection τ hτ a ρ p ha
  rw [RelativeFppfLineSheaf318.topology,GrothendieckTopology.mem_over_iff,Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  apply (Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
  constructor
  · intro x
    obtain ⟨y,hy⟩ := (projection τ hτ a ρ p).surjective x
    exact ⟨PUnit.unit,y,hy⟩
  · intro i
    exact ⟨inferInstance,inferInstance⟩

/-- Every test point is divisible by the original order element after this specific fppf cover,
with the genuine original group operation and the literal covering arrow. -/
lemma local_root (ha : norm a≠0) :
    (Sieve.ofArrows (fun _ : PUnit => Over.mk (coverBase τ hτ a ρ p))
      (fun _ => Over.homMk (projection τ hτ a ρ p) rfl) ∈
      RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℂ)) (Over.mk ρ)) ∧
    PELOriginalUniversalOrderAction318.endomorphism τ hτ (coverBase τ hτ a ρ p) a (root τ hτ a ρ p)=pull τ hτ ρ (projection τ hτ a ρ p) rfl p :=
  ⟨covering τ hτ a ρ p ha,root_equation τ hτ a ρ p⟩
end PELOriginalOrderFppfDivision318
