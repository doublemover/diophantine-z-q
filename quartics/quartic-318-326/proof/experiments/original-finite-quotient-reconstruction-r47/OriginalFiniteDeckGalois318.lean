module
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public section
noncomputable section
namespace OriginalFiniteDeckGalois318
variable {G F L : Type*} [Group G] [Finite G] [Field F] [Field L] [Algebra F L]
  (ρ : G →* (L ≃ₐ[F] L)) (hfaithful : Function.Injective ρ)
  (hfixed : ∀ x : L, (∀ w : G, ρ w x = x) → ∃ r : F, algebraMap F L r = x)

/-- Restriction of the ORIGINAL supplied field automorphisms, not a replacement
action selected from the cardinality of a finite group. -/
@[implicit_reducible] def action : MulSemiringAction G L :=
  MulSemiringAction.compHom L ρ

/-- Faithfulness and the actual quotient-function fixed-field identity give
the original field's Galois group. No algebraicity or degree is assumed. -/
@[expose] def galoisGroup : letI := action ρ; IsGaloisGroup G F L := by
  letI := action ρ
  refine ⟨⟨?_⟩,⟨?_⟩,⟨?_⟩⟩
  · intro v w h
    apply hfaithful
    exact AlgEquiv.ext h
  · intro w r x
    change ρ w (r • x) = r • ρ w x
    exact (ρ w).toLinearEquiv.toLinearMap.map_smul r x
  · intro x hx
    exact hfixed x hx

include ρ hfaithful hfixed in
/-- Finiteness is DERIVED from the original finite action and fixed field. -/
theorem finiteDimensional : FiniteDimensional F L := by
  letI := action ρ
  letI := galoisGroup ρ hfaithful hfixed
  exact IsGaloisGroup.finiteDimensional G F L

include ρ hfaithful hfixed in
/-- Normality and separability are likewise derived for the same field. -/
theorem isGalois : IsGalois F L := by
  letI := action ρ
  letI := galoisGroup ρ hfaithful hfixed
  exact IsGaloisGroup.isGalois G F L

include ρ hfaithful hfixed in
/-- The extension degree is the actual acting group's cardinality. -/
theorem finrank : Module.finrank F L = Nat.card G := by
  letI := action ρ
  letI := galoisGroup ρ hfaithful hfixed
  exact (IsGaloisGroup.card_eq_finrank G F L).symm

/-- Every original base-field automorphism is one of the SAME supplied deck
maps, not merely an abstract isomorphic group element. -/
@[expose] def equivalence : G ≃* (L ≃ₐ[F] L) := by
  letI := action ρ
  letI := galoisGroup ρ hfaithful hfixed
  exact IsGaloisGroup.mulEquivAlgEquiv G F L

lemma equivalence_apply (w : G) : equivalence ρ hfaithful hfixed w = ρ w := by
  apply AlgEquiv.ext
  intro x
  rfl
end OriginalFiniteDeckGalois318
