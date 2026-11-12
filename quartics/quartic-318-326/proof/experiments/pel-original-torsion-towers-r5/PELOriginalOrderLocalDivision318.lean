module
public import PELOriginalSmoothOrderIsogeny318
public import PELOriginalKernelRelationIso318
public section
noncomputable section
namespace PELOriginalOrderLocalDivision318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalOrderSchemeMorphism318
open PELPrincipalOrderCoordinates318 PELOriginalOrderIntegralNorm318
open PELOriginalSchemePointGroup318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
variable {T : Scheme} (ρ : T ⟶ Spec (CommRingCat.of ℂ)) (p : Points τ hτ T ρ)

/-- The literal base change of the original order map along the arbitrary test
point. Its test scheme may be nonreduced or non-finite-type. -/
abbrev Cover := pullback (morphism τ hτ a) p.val
@[expose] def projection : Cover τ hτ a ρ p ⟶ T := pullback.snd _ _
abbrev coverBase : Cover τ hτ a ρ p ⟶ Spec (CommRingCat.of ℂ) := projection τ hτ a ρ p ≫ ρ
@[expose] def root : Points τ hτ (Cover τ hτ a ρ p) (coverBase τ hτ a ρ p) :=
  ⟨pullback.fst _ _,by
    have h := congrArg (fun k => k≫π τ hτ)
      (pullback.condition (f := morphism τ hτ a) (g := p.val))
    simpa only [Category.assoc,over_complex,p.property] using h⟩

/-- Full group-valued root identity after the actual covering map. -/
lemma root_equation : PELOriginalUniversalOrderAction318.endomorphism τ hτ (coverBase τ hτ a ρ p) a (root τ hτ a ρ p)=
    pull τ hτ ρ (projection τ hτ a ρ p) rfl p := by
  apply Subtype.ext
  exact pullback.condition

lemma finite_projection (ha : norm a≠0) : IsFinite (projection τ hτ a ρ p) := by
  letI := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  exact inferInstanceAs (IsFinite (pullback.snd (morphism τ hτ a) p.val))
lemma smooth_projection (ha : norm a≠0) : Smooth (projection τ hτ a ρ p) := by
  letI := PELOriginalSmoothOrderIsogeny318.smooth τ hτ a ha
  exact inferInstanceAs (Smooth (pullback.snd (morphism τ hτ a) p.val))
lemma flat_projection (ha : norm a≠0) : Flat (projection τ hτ a ρ p) := by
  letI := smooth_projection τ hτ a ρ p ha
  infer_instance
lemma surjective_projection (ha : norm a≠0) : Surjective (projection τ hτ a ρ p) := by
  letI : Surjective (morphism τ hτ a) :=
    ⟨PELOriginalOrderNormComposites318.surjective τ hτ a ha⟩
  exact inferInstanceAs (Surjective (pullback.snd (morphism τ hτ a) p.val))

/-- Every original group point over EVERY scheme test admits actual
order-division on a finite, flat, surjective cover of that SAME test. The root
and full over-complex square are explicitly constructed above. -/
lemma local_division (ha : norm a≠0) :
    IsFinite (projection τ hτ a ρ p) ∧ Flat (projection τ hτ a ρ p) ∧
      Surjective (projection τ hτ a ρ p) ∧
      PELOriginalUniversalOrderAction318.endomorphism τ hτ (coverBase τ hτ a ρ p) a (root τ hτ a ρ p)=pull τ hτ ρ (projection τ hτ a ρ p) rfl p :=
  ⟨finite_projection τ hτ a ρ p ha,flat_projection τ hτ a ρ p ha,
    surjective_projection τ hτ a ρ p ha,root_equation τ hτ a ρ p⟩
end PELOriginalOrderLocalDivision318
