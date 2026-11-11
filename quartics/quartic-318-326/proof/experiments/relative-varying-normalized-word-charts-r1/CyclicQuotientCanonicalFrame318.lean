module
public import CyclicQuotientIntertwiner318
public section
noncomputable section
namespace CyclicQuotientCanonicalFrame318
open CyclicQuotientEvaluation318 CyclicQuotientKernel318
universe u
variable {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (ρ : A →ₐ[R] Module.End R M) (σ : A →ₐ[R] Module.End R N)
  (v : M) (w : N)
  (hρ : Function.Surjective (evaluation ρ v))
  (hσ : Function.Surjective (evaluation σ w))
  (hI : ideal ρ v=ideal σ w)

/-- Equal full annihilator ideals construct the actual frame equivalence
through their literal quotient modules, rather than through fibre ranks. -/
@[expose] def equiv : M ≃ₗ[R] N :=
  (quotientEquiv ρ v hρ).symm.trans
    ((Ideal.quotientEquivAlgOfEq R hI).toLinearEquiv.trans (quotientEquiv σ w hσ))

lemma equiv_evaluation (a : A) :
    equiv ρ σ v w hρ hσ hI (evaluation ρ v a)=evaluation σ w a := by
  change equiv ρ σ v w hρ hσ hI (ρ a v)=σ a w
  rw [← quotientEquiv_mk ρ v hρ a]
  simp only [equiv,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
    AlgEquiv.toLinearEquiv_apply,Ideal.quotientEquivAlgOfEq_mk,quotientEquiv_mk]

lemma equiv_intertwines (a : A) (x : M) :
    equiv ρ σ v w hρ hσ hI (ρ a x)=σ a (equiv ρ σ v w hρ hσ hI x) := by
  obtain ⟨b,rfl⟩ := hρ x
  rw [← evaluation_mul,equiv_evaluation,equiv_evaluation,evaluation_mul]

lemma equiv_marked : equiv ρ σ v w hρ hσ hI v=w := by
  have hv : evaluation ρ v 1=v := by change ρ 1 v=v; rw [map_one]; rfl
  have hw : evaluation σ w 1=w := by change σ 1 w=w; rw [map_one]; rfl
  rw [← hv,equiv_evaluation,hw]

/-- On cyclic actions an intertwiner preserving the marked vector is
unique on the WHOLE module. -/
lemma equiv_unique (e : M ≃ₗ[R] N)
    (he : ∀ a x, e (ρ a x)=σ a (e x)) (hv : e v=w) :
    e=equiv ρ σ v w hρ hσ hI := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨a,rfl⟩ := hρ x
  rw [CyclicQuotientIntertwiner318.evaluation_intertwines ρ σ v w e he hv,
    equiv_evaluation]

/-- This is the exact orbit relation: equality of full source ideals iff
there is a genuine invertible frame change preserving the action/vector. -/
lemma ideal_eq_iff_frame : ideal ρ v=ideal σ w ↔
    ∃ e : M ≃ₗ[R] N, (∀ a x, e (ρ a x)=σ a (e x)) ∧ e v=w := by
  constructor
  · intro h
    exact ⟨equiv ρ σ v w hρ hσ h,
      equiv_intertwines ρ σ v w hρ hσ h,equiv_marked ρ σ v w hρ hσ h⟩
  · rintro ⟨e,he,hv⟩
    exact CyclicQuotientIntertwiner318.ideal_eq ρ σ v w e he hv
end CyclicQuotientCanonicalFrame318
