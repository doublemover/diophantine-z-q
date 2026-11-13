module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Etale.Kaehler
public section
noncomputable section
namespace ScalarExtensionTensor318
open CategoryTheory TensorProduct
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]

@[expose] def scalarIdentity :
    (ModuleCat.restrictScalars (algebraMap S T)).obj (ModuleCat.of T T) ≃ₗ[S] T where
  toFun t := t
  invFun t := t
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s t := by
    change algebraMap S T s*(show T from t)=s • (show T from t)
    exact (Algebra.smul_def s (show T from t)).symm

/-- Scalar extension as a category functor is the genuine tensor product with the
    already fixed algebra structure, with all scalar structures explicitly reconciled. -/
@[expose] def tensorEquiv (M : ModuleCat S) :
    (ModuleCat.extendScalars (algebraMap S T)).obj M ≃ₗ[T] T ⊗[S] M := by
  let e := TensorProduct.congr (scalarIdentity (S:=S) (T:=T)) (LinearEquiv.refl S M)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro t z
  induction z using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add z w hz hw =>
    change e (t • z)=t • e z at hz
    change e (t • w)=t • e w at hw
    change e (t • (z+w))=t • e (z+w)
    rw [smul_add,map_add,hz,hw,map_add,smul_add]

theorem tensorEquiv_tmul (M : ModuleCat S) (t : T) (m : M) :
    tensorEquiv (T:=T) M (t ⊗ₜ[S,algebraMap S T] m)=t ⊗ₜ[S] m := rfl

variable {R : Type u} [CommRing R] [Algebra R S] [Algebra R T] [IsScalarTower R S T]

/-- Actual formally étale base change identifies the categorical scalar extension
    of the actual Kähler module with the target's actual Kähler module. -/
@[expose] def kaehlerEquiv [Algebra.FormallyEtale S T] :
    (ModuleCat.extendScalars (algebraMap S T)).obj (ModuleCat.of S (KaehlerDifferential R S)) ≃ₗ[T]
      KaehlerDifferential R T :=
  (tensorEquiv _).trans (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

theorem kaehlerEquiv_tmul [Algebra.FormallyEtale S T] (t : T) (ω : KaehlerDifferential R S) :
    kaehlerEquiv (R:=R) (S:=S) (T:=T) (t ⊗ₜ[S,algebraMap S T] ω)=
      t • KaehlerDifferential.map R R S T ω := by
  change KaehlerDifferential.mapBaseChange R S T (t ⊗ₜ[S] ω)=_
  exact KaehlerDifferential.mapBaseChange_tmul R S T t ω
end ScalarExtensionTensor318
