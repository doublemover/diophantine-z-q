module
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG

@[expose] public section
noncomputable section

open Algebra
open scoped TensorProduct

namespace OriginalSameJExactEtaleDiagonalFactor318

variable {D A : Type*} [CommRing D] [CommRing A] [Algebra D A]

/-- The actual coordinate multiplication of the diagonal in A⊗_D A. -/
abbrev diagonalRead : (A⊗[D]A) →ₐ[D] A :=
  Algebra.TensorProduct.lmul' (S:=A) D

theorem reads_both_legs (a b : A) :
    diagonalRead (a⊗ₜ[D]b)=a*b :=
  Algebra.TensorProduct.lmul'_apply_tmul a b

theorem diagonal_surjective : Function.Surjective (diagonalRead (D:=D) (A:=A)) := by
  intro a
  exact ⟨a⊗ₜ[D]1, (reads_both_legs a 1).trans (mul_one a)⟩

variable [Algebra.EssFiniteType D A] [Algebra.FormallyUnramified D A]

/-- Idempotent for the discarded summand of the very same diagonal.
The proof is the kernel step of Mathlib's
FormallyUnramified.exists_algEquiv_prod, keeping the literal
multiplication kernel rather than choosing an unmarked product iso. -/
theorem discarded :
    ∃ δ : A⊗[D]A, δ*δ=δ ∧
      RingHom.ker (diagonalRead (D:=D) (A:=A)).toRingHom = Ideal.span (Set.singleton δ) := by
  have hFG := KaehlerDifferential.ideal_fg D A
  have hI : IsIdempotentElem (KaehlerDifferential.ideal D A) :=
    (Ideal.cotangent_subsingleton_iff _).mp
      (inferInstanceAs (Subsingleton Ω[A⁄D]))
  obtain ⟨δ,hδ,he⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hFG).mp hI
  exact ⟨δ,hδ.eq,he.trans Ideal.submodule_span_eq⟩

end OriginalSameJExactEtaleDiagonalFactor318

#print axioms OriginalSameJExactEtaleDiagonalFactor318.reads_both_legs
#print axioms OriginalSameJExactEtaleDiagonalFactor318.diagonal_surjective
#print axioms OriginalSameJExactEtaleDiagonalFactor318.discarded
