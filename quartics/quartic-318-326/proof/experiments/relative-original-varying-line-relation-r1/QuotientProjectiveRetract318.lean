module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Quotient.Basic
public section
noncomputable section
namespace QuotientProjectiveRetract318
universe u v w
variable {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N] [Module R N]
  {E : Type w} [AddCommGroup E] [Module R E]
  (out : N →ₗ[R] E) (back : E →ₗ[R] N) (h : back.comp out = LinearMap.id)
  (n : N →ₗ[R] N) (e : E →ₗ[R] E)
  (ho : out.comp n = e.comp out) (hb : back.comp e = n.comp back)

@[expose] def quotientOut : (N ⧸ n.range) →ₗ[R] E ⧸ e.range :=
  n.range.mapQ e.range out (by
    rintro x ⟨y,rfl⟩
    exact ⟨out y,(LinearMap.congr_fun ho y).symm⟩)
@[expose] def quotientBack : (E ⧸ e.range) →ₗ[R] N ⧸ n.range :=
  e.range.mapQ n.range back (by
    rintro x ⟨y,rfl⟩
    exact ⟨back y,(LinearMap.congr_fun hb y).symm⟩)

include h in
lemma retract : (quotientBack back n e hb).comp (quotientOut out n e ho) = LinearMap.id := by
  ext z
  obtain ⟨x,rfl⟩ := n.range.mkQ_surjective z
  change n.range.mkQ (back (out x)) = n.range.mkQ x
  rw [← LinearMap.comp_apply,h,LinearMap.id_apply]

include h in
/-- Quotienting an ACTUAL finite retract along commuting endomorphisms
retains a retract; finite projectivity descends from the concrete free
polynomial quotient, not a generic finite-module kernel claim. -/
theorem finite_projective [Module.Finite R (E ⧸ e.range)] [Module.Projective R (E ⧸ e.range)] :
    Module.Finite R (N ⧸ n.range) ∧ Module.Projective R (N ⧸ n.range) := by
  have hr := retract out back h n e ho hb
  have hs : Function.Surjective (quotientBack back n e hb) := by
    intro x
    exact ⟨quotientOut out n e ho x,LinearMap.congr_fun hr x⟩
  exact ⟨Module.Finite.of_surjective _ hs,
    Module.Projective.of_split (quotientOut out n e ho) (quotientBack back n e hb) hr⟩
end QuotientProjectiveRetract318
