module
public import ContactBoundedHilbertFunctorial318
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TensorProduct.Quotient
public section
noncomputable section
namespace FlatQuotientIdealTensor318
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [Algebra R S] (I : Ideal A) [hflat : Module.Flat R (A ⧸ I)]
abbrev quotient : A →ₗ[R] A ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
abbrev inclusion : I →ₗ[R] A := I.subtype.restrictScalars R
lemma exact : Function.Exact (inclusion R A I) (quotient R A I) := by
  rw [LinearMap.exact_iff]
  ext a
  change Ideal.Quotient.mk I a=0 ↔ ∃ b : I,b.val=a
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => ⟨⟨a,h⟩,rfl⟩,fun ⟨b,h⟩ => h ▸ b.property⟩
include hflat in
/-- Flatness of the QUOTIENT, not of the new coefficient ring, proves
injectivity of the actual extended ideal inclusion. -/
lemma injective : Function.Injective ((inclusion R A I).lTensor S) :=
  LinearMap.lTensor_injective_of_exact_of_flat (quotient R A I)
    (Ideal.Quotient.mkₐ_surjective R I) (inclusion R A I) Subtype.val_injective (exact R A I) S
@[expose] def map : S ⊗[R] I →ₗ[S] S ⊗[R] A :=
  AlgebraTensorModule.lTensor S S (inclusion R A I)
@[expose] def extended : Ideal (S ⊗[R] A) := I.map Algebra.TensorProduct.includeRight.toRingHom
lemma range : LinearMap.range (map R A S I)=(extended R A S I).restrictScalars S :=
  AlgebraTensorModule.range_lTensor_idealMap S S I
/-- The WHOLE extended ideal is precisely coefficient tensor of the
original ideal, with the actual inclusion into the source algebra fixed. -/
@[expose] def equivalence : S ⊗[R] I ≃ₗ[S] extended R A S I :=
  LinearEquiv.ofInjective (map R A S I) (injective R A S I) ≪≫ₗ
    LinearEquiv.ofEq _ _ (range R A S I)
lemma equivalence_coe (z : S ⊗[R] I) : (equivalence R A S I z).val=map R A S I z := rfl
lemma equivalence_tmul (s : S) (i : I) : (equivalence R A S I (s ⊗ₜ[R] i)).val=s ⊗ₜ[R] i.val := rfl
end FlatQuotientIdealTensor318
