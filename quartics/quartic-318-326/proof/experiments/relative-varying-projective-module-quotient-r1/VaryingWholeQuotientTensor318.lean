module
public import VaryingWholeIdealFamily318
public import Mathlib.RingTheory.TensorProduct.Quotient
public section
noncomputable section
namespace VaryingWholeQuotientTensor318
open scoped TensorProduct
universe u
variable (R A S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (I : Ideal (S ⊗[R] A))
@[expose] def source : (S ⊗[R] A) →ₐ[S] (T ⊗[R] A) :=
  Algebra.TensorProduct.rTensor A (Algebra.ofId S T)
@[expose] def ideal : Ideal (T ⊗[R] A) := I.map (source R A S T).toRingHom
/-- Full-ideal version of the scalar-extension quotient equivalence.
It applies to EVERY ideal, not just principal ideals or cyclic frames. -/
set_option backward.isDefEq.respectTransparency false in
attribute [local ext high] Ideal.Quotient.algHom_ext in
@[expose] def equivalence : T ⊗[S] ((S ⊗[R] A) ⧸ I) ≃ₐ[T]
    ((T ⊗[R] A) ⧸ ideal R A S T I) := by
  let φ := source R A S T
  let ψ : (T ⊗[R] A) →ₐ[T] T ⊗[S] ((S ⊗[R] A) ⧸ I) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
        ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight))
      (fun _ _ => .all _ _)
  have hψφ : (ψ.restrictScalars S).comp φ=
      (Algebra.TensorProduct.includeRight.restrictScalars S).comp (Ideal.Quotient.mkₐ _ I) := by
    ext <;> simp [ψ,φ,source]
  have hker : ideal R A S T I ≤ RingHom.ker ψ.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change ψ (φ a)=0
    have h := congrArg (fun g : (S ⊗[R] A) →ₐ[S] T ⊗[S] ((S ⊗[R] A) ⧸ I) => g a) hψφ
    change ψ (φ a)=Algebra.TensorProduct.includeRight (Ideal.Quotient.mk I a) at h
    rw [h,Ideal.Quotient.eq_zero_iff_mem.mpr ha,map_zero]
  exact AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (Ideal.quotientMapₐ _ φ (Ideal.map_le_iff_le_comap.mp le_rfl))
      (fun _ _ => .all _ _))
    (Ideal.Quotient.liftₐ _ ψ hker)
    (by ext <;> simp [ψ,φ,source])
    (by ext <;> simp [φ,ψ,source])
lemma equivalence_tmul (t : T) (s : S) (a : A) :
    equivalence R A S T I (t ⊗ₜ[S] Ideal.Quotient.mk I (s ⊗ₜ[R] a))=
      Ideal.Quotient.mk _ ((t*algebraMap S T s) ⊗ₜ[R] a) := by
  simp [equivalence,source,← Ideal.Quotient.mk_algebraMap,← map_mul]
/-- This is exactly the source coefficient map already used by the
geometric classifier, with the existing scalar tower. -/
lemma source_eq : (source R A S T).toRingHom=
    (VaryingNormalizedIdealBaseChange318.sourceMap R A S T
      (IsScalarTower.toAlgHom R S T)).toRingHom := rfl
end VaryingWholeQuotientTensor318
