module
public import IntegralEtaleCotangent318
public section
noncomputable section
namespace EvaluatedCotangentExt318
open scoped TensorProduct
variable (R A T : Type*) [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra A T]
  {M : Type*} [AddCommGroup M] [Module T M]

/-- Evaluated universal differentials generate the entire evaluated
cotangent module. This proves uniqueness of actual maps, not just rank. -/
theorem hom_ext (f g : T ⊗[A] KaehlerDifferential R A →ₗ[T] M)
    (h : ∀ a : A, f ((1:T) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      g ((1:T) ⊗ₜ[A] KaehlerDifferential.D R A a)) : f=g := by
  have he : ∀ z : KaehlerDifferential R A, ∀ k : T,
      f (k ⊗ₜ[A] z)=g (k ⊗ₜ[A] z) := by
    intro z
    have hz : z ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨a,rfl⟩ k
      have hk : k ⊗ₜ[A] KaehlerDifferential.D R A a =
          k • ((1:T) ⊗ₜ[A] KaehlerDifferential.D R A a) := by
        rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
      simp only [hk,map_smul,h a]
    · intro k
      simp only [TensorProduct.tmul_zero,map_zero]
    · intro x y _ _ hx hy k
      simp only [TensorProduct.tmul_add,map_add,hx,hy]
    · intro a z _ hz k
      simp only [←TensorProduct.smul_tmul]
      exact hz (a • k)
  apply TensorProduct.AlgebraTensorModule.ext
  intro k z
  exact he z k

/-- The same uniqueness statement for equivalences, retaining their
literal maps on each evaluated universal differential. -/
theorem equiv_ext (f g : T ⊗[A] KaehlerDifferential R A ≃ₗ[T] M)
    (h : ∀ a : A, f ((1:T) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      g ((1:T) ⊗ₜ[A] KaehlerDifferential.D R A a)) : f=g := by
  apply LinearEquiv.toLinearMap_injective
  exact hom_ext R A T f.toLinearMap g.toLinearMap h
end EvaluatedCotangentExt318
