module
public import SelectedActualNumberFieldPlaceTrait318
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public section
noncomputable section

open NumberField TensorProduct
open scoped TensorProduct
open SelectedActualNumberFieldPlaceTrait318

namespace SelectedActualLocalHodgeLattice318

variable {L : Type*} [Field L] [NumberField L]
variable (v : FinitePlace L)
variable (H : Type*) [AddCommGroup H] [Module (𝓞 L) H]
attribute [local instance] intoL

/-- The local Hodge lattice is the actual localization of the ONE
global module. It is not an independent lattice for each place. -/
abbrev Local := Trait v ⊗[𝓞 L] H

@[expose] def toGeneric : Local v H →ₗ[Trait v] L ⊗[𝓞 L] H :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap (Trait v) L)
    (LinearMap.id : H →ₗ[𝓞 L] H)

theorem toGeneric_tmul (r : Trait v) (a : H) :
    toGeneric v H (r ⊗ₜ[𝓞 L] a) = algebraMap (Trait v) L r ⊗ₜ[𝓞 L] a := by
  rw [toGeneric,TensorProduct.AlgebraTensorModule.map_tmul] <;> rfl

theorem toGeneric_injective [Module.Flat (𝓞 L) H] : Function.Injective (toGeneric v H) := by
  let f : Trait v →ₗ[𝓞 L] L := (Algebra.linearMap (Trait v) L).restrictScalars (𝓞 L)
  have hf : Function.Injective f := IsFractionRing.injective (Trait v) L
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := H) f hf
  have he (z : Local v H) : toGeneric v H z = f.rTensor H z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r a =>
        rw [toGeneric_tmul,LinearMap.rTensor_tmul]
        rfl
    | add x y hx hy => rw [map_add,map_add,hx,hy]
  intro x y h
  exact hi ((he x).symm.trans (h.trans (he y)))

instance localTorsionFree [Module.Flat (𝓞 L) H] : Module.IsTorsionFree (Trait v) (Local v H) := by
  letI : Module.IsTorsionFree (Trait v) (L ⊗[𝓞 L] H) :=
    Module.IsTorsionFree.comap (algebraMap (Trait v) L)
      (fun r hr => isRegular_iff_ne_zero.mpr (by
        intro hz
        exact (isRegular_iff_ne_zero.mp hr)
          (IsFractionRing.injective (Trait v) L (hz.trans (map_zero _).symm))))
      (fun r a => IsScalarTower.algebraMap_smul L r a)
  exact Function.Injective.moduleIsTorsionFree (toGeneric v H)
    (toGeneric_injective v H) (map_smul _)

/-- Extend scalars across the actual intermediate local ring. -/
@[expose] def genericAfterLocal :
    L ⊗[Trait v] Local v H ≃ₗ[L] L ⊗[𝓞 L] H :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 L) (Trait v) L L H

theorem genericAfterLocal_one (a : H) :
    genericAfterLocal v H ((1:L) ⊗ₜ[Trait v] ((1:Trait v) ⊗ₜ[𝓞 L] a)) =
      (1:L) ⊗ₜ[𝓞 L] a := by
  unfold genericAfterLocal
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,one_smul]

variable {G : Type*} [AddCommGroup G] [Module L G]

/-- Pullback of the global generic Abel--Jacobi comparison to the
localized global Hodge lattice. This is a literal tensor identity. -/
@[expose] def localAJ (AJ : L ⊗[𝓞 L] H ≃ₗ[L] G) : L ⊗[Trait v] Local v H ≃ₗ[L] G :=
  (genericAfterLocal v H).trans AJ

theorem localAJ_one (AJ : L ⊗[𝓞 L] H ≃ₗ[L] G) (a : H) :
    localAJ v H AJ ((1:L) ⊗ₜ[Trait v] ((1:Trait v) ⊗ₜ[𝓞 L] a)) =
      AJ ((1:L) ⊗ₜ[𝓞 L] a) := by
  rw [localAJ,LinearEquiv.trans_apply,genericAfterLocal_one]

/-- Finite flat global Hodge modules have a basis of precisely the
original ordered size on the actual DVR, with no extra rank input. -/
def localBasis [Module.Finite (𝓞 L) H] [Module.Flat (𝓞 L) H] {g : ℕ}
    (AJ : L ⊗[𝓞 L] H ≃ₗ[L] G) (ω : Module.Basis (Fin g) L G) :
    Module.Basis (Fin g) (Trait v) (Local v H) := by
  let b : Σ k : ℕ, Module.Basis (Fin k) (Trait v) (Local v H) :=
    Module.basisOfFiniteTypeTorsionFree'
  let bL := (b.2.baseChange L).map (localAJ v H AJ)
  have h1 : Module.finrank L G = b.1 := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis bL
  have h2 : Module.finrank L G = g := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis ω
  exact b.2.reindex (finCongr (h1.symm.trans h2))

end SelectedActualLocalHodgeLattice318

#print axioms SelectedActualLocalHodgeLattice318.localAJ_one
#print axioms SelectedActualLocalHodgeLattice318.localBasis
