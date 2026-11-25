module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Coprime.Basic
public section
noncomputable section

namespace OriginalR8ActualGenericFrameLabels318

open Matrix

universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The literal first generator of an ordered frame. -/
@[expose] def e0 : Fin 2 → R := Pi.single (0 : Fin 2) 1

/-- A primitive column over the actual composite level ring is extendible
to a genuine full frame; a field assumption on the level ring is wrong. -/
theorem complete_first (a b : R) (hp : IsCoprime a b) :
    ∃ U : Matrix.GeneralLinearGroup (Fin 2) R,
      (U : Matrix (Fin 2) (Fin 2) R) 0 0 = a ∧
      (U : Matrix (Fin 2) (Fin 2) R) 1 0 = b := by
  obtain ⟨r,s,hrs⟩ := hp
  let A : Matrix (Fin 2) (Fin 2) R := !![a,-s;b,r]
  have hd : Matrix.det A = 1 := by
    rw [show Matrix.det A = a*r - (-s)*b by exact Matrix.det_fin_two_of a (-s) b r]
    simpa only [neg_mul,sub_neg_eq_add,mul_comm a r] using hrs
  have hu : IsUnit (Matrix.det A) := hd.symm ▸ isUnit_one
  exact ⟨Matrix.GeneralLinearGroup.mk'' A hu,rfl,rfl⟩

/-- The exact orbit relation for forgetting the second generator:
the change of basis preserves the full primitive first-point orbit
under the actual scalar subgroup. Both frames live on the same
geometric torsion module. -/
theorem first_orbit (S : Subgroup Rˣ)
    (P Q : (Fin 2 → R) ≃ₗ[R] M) :
    (∃ A : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R),
       A.trans P = Q ∧ ∃ s : S, A e0 = ((s : Rˣ) : R) • e0) ↔
      ∃ s : S, Q e0 = ((s : Rˣ) : R) • P e0 := by
  constructor
  · rintro ⟨A,hAQ,s,hs⟩
    refine ⟨s,?_⟩
    have h := congrArg (fun E : (Fin 2 → R) ≃ₗ[R] M => E e0) hAQ
    exact h.symm.trans (by
      change P (A e0) = _
      rw [hs,map_smul])
  · rintro ⟨s,hs⟩
    let A := Q.trans P.symm
    refine ⟨A,?_,s,?_⟩
    · ext x
      exact P.apply_symm_apply (Q x)
    · apply P.injective
      change P (P.symm (Q e0)) = P (((s : Rˣ) : R) • e0)
      rw [LinearEquiv.apply_symm_apply,map_smul,hs]

end OriginalR8ActualGenericFrameLabels318

#print axioms OriginalR8ActualGenericFrameLabels318.complete_first
#print axioms OriginalR8ActualGenericFrameLabels318.first_orbit
