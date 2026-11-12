module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public section
noncomputable section
namespace BaseChangingDifferentialTensor318
open scoped TensorProduct
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
  (f : A →ₐ[R] B)
@[expose] def differential : KaehlerDifferential R A →ₗ[R] KaehlerDifferential S B := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  exact (KaehlerDifferential.map R S A B).restrictScalars R

theorem differential_D (a : A) : differential (S:=S) f (KaehlerDifferential.D R A a)=
    KaehlerDifferential.D S B (f a) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  exact KaehlerDifferential.map_D R S A B a

theorem differential_smul (a : A) (ω : KaehlerDifferential R A) :
    differential (S:=S) f (a • ω)=f a • differential (S:=S) f ω := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  change KaehlerDifferential.map R S A B (a • ω)=algebraMap A B a • KaehlerDifferential.map R S A B ω
  rw [LinearMap.map_smul,IsScalarTower.algebraMap_smul]

@[expose] def differentialSemilinear :
    KaehlerDifferential R A →ₛₗ[f.toRingHom] KaehlerDifferential S B where
  __ := (differential (S:=S) f).toAddMonoidHom
  map_smul' := differential_smul (S:=S) f

@[expose] def balanced : KaehlerDifferential R A →ₛₗ[f.toRingHom]
    KaehlerDifferential R A →ₛₗ[f.toRingHom]
      (KaehlerDifferential S B ⊗[B] KaehlerDifferential S B) where
  toFun ω :=
    { toFun := fun η => differential (S:=S) f ω ⊗ₜ[B] differential (S:=S) f η
      map_add' := fun η ξ => by rw [map_add,TensorProduct.tmul_add]
      map_smul' := fun a η => by rw [differential_smul,TensorProduct.tmul_smul] }
  map_add' ω η := by
    ext ξ
    change differential (S:=S) f (ω+η) ⊗ₜ[B] differential (S:=S) f ξ=
      (differential (S:=S) f ω ⊗ₜ[B] differential (S:=S) f ξ)+
        (differential (S:=S) f η ⊗ₜ[B] differential (S:=S) f ξ)
    rw [map_add,TensorProduct.add_tmul]
  map_smul' a ω := by
    ext η
    change differential (S:=S) f (a • ω) ⊗ₜ[B] differential (S:=S) f η=
      f a • (differential (S:=S) f ω ⊗ₜ[B] differential (S:=S) f η)
    rw [differential_smul,←TensorProduct.smul_tmul']

/-- The universal balanced tensor lift is an actual map OUT OF the
integral tensor square. It is independent of a chosen pure presentation. -/
@[expose] def tensorMap :
    (KaehlerDifferential R A ⊗[A] KaehlerDifferential R A) →ₛₗ[f.toRingHom]
      (KaehlerDifferential S B ⊗[B] KaehlerDifferential S B) :=
  TensorProduct.lift (balanced (S:=S) f)

theorem tensorMap_tmul (ω η : KaehlerDifferential R A) :
    tensorMap (S:=S) f (ω ⊗ₜ[A] η)=
      differential (S:=S) f ω ⊗ₜ[B] differential (S:=S) f η :=
  TensorProduct.lift.tmul _ _ _

/-- Actual tensor pullback on pure tensors and scalar multiples. Its
inputs are the genuine universal differential modules of the two bases. -/
@[expose] def pureImage (a : A) (ω η : KaehlerDifferential R A) :
    KaehlerDifferential S B ⊗[B] KaehlerDifferential S B :=
  f a • (differential (S:=S) f ω ⊗ₜ[B] differential (S:=S) f η)

theorem pureImage_D (a x y : A) :
    pureImage (S:=S) f a (KaehlerDifferential.D R A x) (KaehlerDifferential.D R A y)=
      f a • (KaehlerDifferential.D S B (f x) ⊗ₜ[B] KaehlerDifferential.D S B (f y)) := by
  rw [pureImage,differential_D,differential_D]
theorem tensorMap_weighted (a : A) (ω η : KaehlerDifferential R A) :
    tensorMap (S:=S) f (a • (ω ⊗ₜ[A] η))=pureImage (S:=S) f a ω η := by
  rw [LinearMap.map_smulₛₗ,tensorMap_tmul]
  rfl

end BaseChangingDifferentialTensor318
