module
public import SelectedActualIdentityCotangent318
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.Tactic.Ring
public section
noncomputable section

namespace SelectedSplitIdentityNonflat318

open TensorProduct SelectedActualIdentityCotangent318
open scoped TensorProduct

variable {R B T : Type*} [CommRing R] [CommRing B] [CommRing T]
variable [Algebra R B] [Algebra R T]
variable (ε : B →ₐ[R] R)

/-- Split the actual augmentation, before any specialization. -/
private def subtractAug : B →ₗ[R] I ε where
  toFun b := ⟨b - algebraMap R B (ε b), RingHom.mem_ker.mpr (by simp)⟩
  map_add' x y := Subtype.ext (by simp [map_add] <;> ring)
  map_smul' s x := Subtype.ext (by
    change (s • x) - algebraMap R B (ε (s • x)) =
      s • (x - algebraMap R B (ε x))
    simp [Algebra.smul_def,map_mul,mul_sub])

private theorem subtractAug_onIdeal (b : I ε) : subtractAug ε (b:B) = b := by
  have h := RingHom.mem_ker.mp b.property
  apply Subtype.ext
  simp only [subtractAug,h,map_zero,sub_zero]

private def splitToCotangent : B →ₗ[R] (I ε).Cotangent :=
  ((I ε).toCotangent.restrictScalars R) ∘ₗ subtractAug ε

private theorem splitToCotangent_kills :
    (((I ε)^2).restrictScalars R) ≤ (splitToCotangent ε).ker := by
  intro b hb
  change b ∈ (I ε)^2 at hb
  let bI : I ε := ⟨b,Ideal.pow_le_self (by decide : (2:ℕ) ≠ 0) hb⟩
  change (I ε).toCotangent (subtractAug ε (bI:B)) = 0
  rw [subtractAug_onIdeal]
  exact (Ideal.toCotangent_eq_zero _ _).2 hb

/-- A genuine retraction of the canonical injection into B/I². This
replaces flatness in the stock cotangent base-change argument. -/
private def retract : B ⧸ (I ε)^2 →ₗ[R] (I ε).Cotangent :=
  ((((I ε)^2).restrictScalars R).liftQ (splitToCotangent ε) (splitToCotangent_kills ε)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R ((I ε)^2)).symm.toLinearMap

private theorem retract_right (x : (I ε).Cotangent) :
    retract ε ((I ε).cotangentToQuotientSquare x) = x := by
  obtain ⟨b,rfl⟩ := Ideal.toCotangent_surjective _ x
  rw [Ideal.toCotangent_to_quotient_square]
  change (((I ε)^2).restrictScalars R).liftQ (splitToCotangent ε) (splitToCotangent_kills ε)
    ((Submodule.Quotient.restrictScalarsEquiv R ((I ε)^2)).symm (Submodule.Quotient.mk (b:B))) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk,Submodule.liftQ_apply]
  change (I ε).toCotangent (subtractAug ε (b:B)) = _
  rw [subtractAug_onIdeal]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual conormal's canonical base-change hom is injective even
on nonflat evaluation into the arithmetic trait. The hypotheses
are precisely those of a split identity augmentation; no family
smoothness or flatness of the evaluation ring map is asserted. -/
theorem canonical_injective_noFlat :
    Function.Injective ((I ε).tensorCotangentHom R T) := by
  let a : B →+* T ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
  let f : ((I ε).map a).Cotangent →ₗ[T] T ⊗[R] B ⧸ ((I ε).map a)^2 :=
    (Ideal.cotangentToQuotientSquare _).restrictScalars T
  let g : T ⊗[R] (I ε).Cotangent →ₗ[T] T ⊗[R] (B ⧸ (I ε)^2) :=
    AlgebraTensorModule.lTensor T T (I ε).cotangentToQuotientSquare
  let e : T ⊗[R] (B ⧸ (I ε)^2) ≃ₐ[T] T ⊗[R] B ⧸ ((I ε).map a)^2 :=
    (Algebra.TensorProduct.tensorQuotientEquiv _ _ _ _).trans
      (Ideal.quotientEquivAlgOfEq T (Ideal.map_pow _ _ _))
  have square : f ∘ₗ (I ε).tensorCotangentHom R T = e.toLinearMap ∘ₗ g := by
    ext x
    obtain ⟨x,rfl⟩ := Ideal.toCotangent_surjective _ x
    dsimp [f,g,e]
    rw [Ideal.tensorCotangentHom_tmul,one_smul,Ideal.toCotangent_to_quotient_square]
    simp
  let rT := AlgebraTensorModule.lTensor T T (retract ε)
  have split : Function.LeftInverse rT g := by
    intro z
    have h' : ∀ z, rT (g z) = z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => rw [map_add,map_add,hx,hy]
      | tmul t x =>
          change AlgebraTensorModule.lTensor T T (retract ε)
            (AlgebraTensorModule.lTensor T T ((I ε).cotangentToQuotientSquare.restrictScalars R)
              (t ⊗ₜ[R] x)) = t ⊗ₜ[R] x
          rw [AlgebraTensorModule.lTensor_tmul,AlgebraTensorModule.lTensor_tmul]
          simp only [LinearMap.coe_restrictScalars,retract_right]
    exact h' z
  have inj : Function.Injective (f ∘ₗ (I ε).tensorCotangentHom R T) := by
    rw [square,LinearMap.coe_comp]
    exact e.injective.comp split.injective
  exact Function.Injective.of_comp inj

/-- The canonical equivalent extension of the actual affine Hodge
conormal, with no flatness premise at the residue or trait. -/
def identityBaseChangeNoFlat :
    T ⊗[R] (I ε).Cotangent ≃ₗ[T] (RingHom.ker (baseAug (T:=T) ε).toRingHom).Cotangent := by
  rw [ker_baseAug]
  exact LinearEquiv.ofBijective ((I ε).tensorCotangentHom R T)
    ⟨canonical_injective_noFlat ε, (I ε).tensorCotangentHom_surjective R T⟩

end SelectedSplitIdentityNonflat318

#print axioms SelectedSplitIdentityNonflat318.canonical_injective_noFlat
#print axioms SelectedSplitIdentityNonflat318.identityBaseChangeNoFlat
