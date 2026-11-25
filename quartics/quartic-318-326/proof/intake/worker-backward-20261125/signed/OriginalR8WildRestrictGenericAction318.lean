module
public import OriginalR8WildFixedIntegralOrder318
public import OriginalR8WildFixedFlatBase318
public section
noncomputable section

namespace OriginalR8WildRestrictGenericAction318

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z
variable {A : Type u} [CommRing A] {L : Type v} [Field L] [Algebra A L]
variable {M : Type w} [Field M] [Algebra L M] [Algebra A M] [IsScalarTower A L M]
variable {B : Type z} [CommRing B] [Algebra A B] [Algebra B M] [IsScalarTower A B M]
variable [IsIntegralClosure B A M]

private theorem integral_image (σ : M ≃ₐ[L] M) (b : B) :
    IsIntegral A (σ (algebraMap B M b)) := by
  have hb : IsIntegral A (algebraMap B M b) :=
    (IsIntegralClosure.isIntegral_iff (A := B)).mpr ⟨b,rfl⟩
  exact IsIntegral.map ((σ.restrictScalars A).toAlgHom) hb

@[expose] def restrictHom (σ : M ≃ₐ[L] M) : B →ₐ[A] B where
  toFun b := IsIntegralClosure.mk' B (σ (algebraMap B M b)) (integral_image σ b)
  map_one' := by
    apply IsIntegralClosure.algebraMap_injective B A M
    simp only [IsIntegralClosure.algebraMap_mk',map_one]
  map_zero' := by
    apply IsIntegralClosure.algebraMap_injective B A M
    simp only [IsIntegralClosure.algebraMap_mk',map_zero]
  map_add' x y := by
    apply IsIntegralClosure.algebraMap_injective B A M
    simp only [IsIntegralClosure.algebraMap_mk',map_add]
  map_mul' x y := by
    apply IsIntegralClosure.algebraMap_injective B A M
    simp only [IsIntegralClosure.algebraMap_mk',map_mul]
  commutes' x := by
    apply IsIntegralClosure.algebraMap_injective B A M
    rw [IsIntegralClosure.algebraMap_mk', ← IsScalarTower.algebraMap_apply A B M x,
      IsScalarTower.algebraMap_apply A L M x, σ.commutes]

@[simp] theorem restrictHom_read (σ : M ≃ₐ[L] M) (b : B) :
    algebraMap B M (restrictHom σ b) = σ (algebraMap B M b) :=
  IsIntegralClosure.algebraMap_mk' _ _

/-- The actual generic automorphism acts on the exact same normalized finite
order. This implements the restriction at the held integral-closure
embedding, without an independently provided action on the arithmetic order. -/
@[expose] def restrictEquiv (σ : M ≃ₐ[L] M) : B ≃ₐ[A] B :=
  AlgEquiv.ofAlgHom (restrictHom σ) (restrictHom σ.symm)
    (by
      ext b
      apply IsIntegralClosure.algebraMap_injective B A M
      simp only [AlgHom.comp_apply, AlgHom.id_apply, restrictHom_read, AlgEquiv.apply_symm_apply])
    (by
      ext b
      apply IsIntegralClosure.algebraMap_injective B A M
      simp only [AlgHom.comp_apply, AlgHom.id_apply, restrictHom_read, AlgEquiv.symm_apply_apply])

@[simp] theorem restrictEquiv_read (σ : M ≃ₐ[L] M) (b : B) :
    algebraMap B M (restrictEquiv σ b) = σ (algebraMap B M b) :=
  restrictHom_read σ b

@[expose] def action : (M ≃ₐ[L] M) →* (B ≃ₐ[A] B) where
  toFun := restrictEquiv
  map_one' := by
    ext b
    apply IsIntegralClosure.algebraMap_injective B A M
    simp only [restrictEquiv_read, AlgEquiv.one_apply]
  map_mul' f g := by
    ext b
    apply IsIntegralClosure.algebraMap_injective B A M
    simp only [AlgEquiv.mul_apply,restrictEquiv_read]

/-- Flat fixed elements for the actually restricted generic primitive/frame
action; the one remaining geometric hypothesis is the genuine whole-field
generic invariant identity, not any separate integral or flat action. -/
theorem flat_fixed_of_generic {C G : Type*} [CommRing C] [Algebra A C] [Module.Flat A C]
    [IsDomain A] [IsIntegrallyClosed A] [IsFractionRing A L] [Group G] [Fintype G] [DecidableEq G]
    (σ : G →* (M ≃ₐ[L] M))
    (generic_fixed : ∀ m : M, (∀ g : G, σ g m = m) → ∃ t : L, algebraMap L M t = m)
    (z : C ⊗[A] B) :
    (∀ g : G, ((restrictEquiv (σ g)).toLinearMap.lTensor C) z = z) ↔
      ∃ c : C, c ⊗ₜ[A] (1 : B) = z := by
  apply OriginalR8WildFixedFlatBase318.fixed_after_flat
  intro b
  rw [← OriginalR8WildFixedIntegralOrder318.fixed_order σ generic_fixed b]
  constructor
  · intro h g
    rw [← restrictEquiv_read,h g]
  · intro h g
    exact IsIntegralClosure.algebraMap_injective B A M ((restrictEquiv_read (σ g) b).trans (h g))

end OriginalR8WildRestrictGenericAction318

#print axioms OriginalR8WildRestrictGenericAction318.restrictEquiv_read
#print axioms OriginalR8WildRestrictGenericAction318.action
#print axioms OriginalR8WildRestrictGenericAction318.flat_fixed_of_generic
