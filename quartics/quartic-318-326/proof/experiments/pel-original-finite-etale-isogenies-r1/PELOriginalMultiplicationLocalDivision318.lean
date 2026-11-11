module
public import PELOriginalMultiplicationSmooth318
public import PELOriginalKernelRelationIso318
public section
noncomputable section
namespace PELOriginalMultiplicationLocalDivision318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalIntegerMultiplication318
open PELOriginalSchemePointGroup318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)
variable {T : Scheme} (ρ : T ⟶ Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)

/-- The literal base change of multiplication along the arbitrary test
point. Its test scheme may be nonreduced or non-finite-type. -/
abbrev Cover := pullback (multiplication τ hτ n) p.val
@[expose] def projection : Cover τ hτ n ρ p ⟶ T := pullback.snd _ _
abbrev coverBase : Cover τ hτ n ρ p ⟶ Spec (CommRingCat.of ℂ) := projection τ hτ n ρ p ≫ ρ
@[expose] def root : Points τ hτ (Cover τ hτ n ρ p) (coverBase τ hτ n ρ p) :=
  ⟨pullback.fst _ _,by
    have h := congrArg (fun k => k≫π τ hτ)
      (pullback.condition (f := multiplication τ hτ n) (g := p.val))
    simpa only [Category.assoc,over_complex,p.property] using h⟩

/-- Full group-valued root identity after the actual covering map. -/
lemma root_equation : n • root τ hτ n ρ p=
    pull τ hτ ρ (projection τ hτ n ρ p) rfl p := by
  apply Subtype.ext
  rw [←PELOriginalIntegerMultiplication318.test_action τ hτ n
    (root τ hτ n ρ p).val (root τ hτ n ρ p).property]
  exact pullback.condition

lemma finite_projection (hn : n≠0) : IsFinite (projection τ hτ n ρ p) := by
  letI := PELOriginalFiniteSurjectiveMultiplication318.finite τ hτ n hn
  exact inferInstanceAs (IsFinite (pullback.snd (multiplication τ hτ n) p.val))
lemma smooth_projection (hn : n≠0) : Smooth (projection τ hτ n ρ p) := by
  letI := PELOriginalMultiplicationSmooth318.smooth τ hτ n hn
  exact inferInstanceAs (Smooth (pullback.snd (multiplication τ hτ n) p.val))
lemma flat_projection (hn : n≠0) : Flat (projection τ hτ n ρ p) := by
  letI := smooth_projection τ hτ n ρ p hn
  infer_instance
lemma surjective_projection (hn : n≠0) : Surjective (projection τ hτ n ρ p) := by
  letI : Surjective (multiplication τ hτ n) :=
    ⟨PELOriginalFiniteSurjectiveMultiplication318.surjective τ hτ n hn⟩
  exact inferInstanceAs (Surjective (pullback.snd (multiplication τ hτ n) p.val))

/-- Every original group point over EVERY scheme test admits actual
n-division on a finite, flat, surjective cover of that SAME test. The root
and full over-complex square are explicitly constructed above. -/
lemma local_division (hn : n≠0) :
    IsFinite (projection τ hτ n ρ p) ∧ Flat (projection τ hτ n ρ p) ∧
      Surjective (projection τ hτ n ρ p) ∧
      n • root τ hτ n ρ p=pull τ hτ ρ (projection τ hτ n ρ p) rfl p :=
  ⟨finite_projection τ hτ n ρ p hn,flat_projection τ hτ n ρ p hn,
    surjective_projection τ hτ n ρ p hn,root_equation τ hτ n ρ p⟩
end PELOriginalMultiplicationLocalDivision318
