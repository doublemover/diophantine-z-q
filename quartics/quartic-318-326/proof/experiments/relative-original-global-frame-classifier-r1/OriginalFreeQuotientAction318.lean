module
public import CyclicQuotientMatrices318
public section
noncomputable section
namespace OriginalFreeQuotientAction318
open CyclicQuotientEvaluation318
universe u
variable {R A Q : Type u} [CommRing R] [CommRing A] [CommRing Q]
  [Algebra R A] [Algebra R Q]
variable (q : A →ₐ[R] Q)

/-- Multiplication on the ACTUAL quotient, with no chosen replacement
multiplication table. This produces the commuting action for chart recovery. -/
@[expose] def action : A →ₐ[R] Module.End R Q := (Algebra.lmul R Q).comp q

lemma action_apply (a : A) (x : Q) : action q a x = q a * x := rfl

lemma evaluation_one (a : A) : evaluation (action q) (1 : Q) a = q a :=
  mul_one (q a)

lemma cyclic (h : Function.Surjective q) :
    Function.Surjective (evaluation (action q) (1 : Q)) := by
  intro x
  obtain ⟨a,ha⟩ := h x
  exact ⟨a,(evaluation_one q a).trans ha⟩

/-- Recover exactly the original kernel ideal, not its radical, saturation,
or fiberwise approximation. In particular nilpotent relations survive. -/
lemma ideal_eq_kernel : ideal (action q) (1 : Q) = RingHom.ker q := by
  ext a
  change evaluation (action q) (1 : Q) a = 0 ↔ q a = 0
  rw [evaluation_one]

@[expose] def originalQuotient (h : Function.Surjective q) :
    (A ⧸ RingHom.ker q) ≃ₐ[R] Q := Ideal.quotientKerAlgEquivOfSurjective h

lemma originalQuotient_mk (h : Function.Surjective q) (a : A) :
    originalQuotient q h (Ideal.Quotient.mk (RingHom.ker q) a) = q a :=
  Ideal.quotientKerAlgEquivOfSurjective_mk h a
end OriginalFreeQuotientAction318
