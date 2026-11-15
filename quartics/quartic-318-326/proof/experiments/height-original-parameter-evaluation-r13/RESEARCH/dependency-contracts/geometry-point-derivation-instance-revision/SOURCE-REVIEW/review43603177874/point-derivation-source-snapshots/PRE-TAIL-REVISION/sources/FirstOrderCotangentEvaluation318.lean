module
public import FourRootFirstOrderPoint318
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public section
noncomputable section
namespace FirstOrderCotangentEvaluation318
open scoped TensorProduct
variable (V A K : Type*) [CommRing V] [CommRing A] [Field K]
  [Algebra V A] [Algebra V K]

section FieldPoint
variable (f : A →ₐ[V] K) (L : A →ₐ[V] TrivSqZeroExt K K)
  (hL : ∀ a,(L a).fst=f a)

/-- Extract the derivative of the CONSTRUCTED first-order lift. Its exact
point action is explicitly fixed in both type and body, not registered as
an instance with an undetermined hidden point parameter. -/
@[expose] def derivation :
    letI : Algebra A K := f.toRingHom.toAlgebra
    Derivation V A K := by
  letI : Algebra A K := f.toRingHom.toAlgebra
  letI : IsScalarTower V A K := IsScalarTower.of_algHom f
  exact
    { toLinearMap := ((TrivSqZeroExt.sndHom K K).restrictScalars V).comp L.toLinearMap
      map_one_eq_zero' := by
        change (L 1).snd=0
        rw [map_one]
        rfl
      leibniz' := fun a b => by
        change (L (a*b)).snd=f a*(L b).snd+f b*(L a).snd
        rw [map_mul,TrivSqZeroExt.snd_mul]
        change (L a).fst*(L b).snd+(L a).snd*(L b).fst=f a*(L b).snd+f b*(L a).snd
        rw [hL a,hL b]
        ring }

/-- The native universal differential map, with no assumed derivation or
free cotangent frame. -/
@[expose] def cotangentMap :
    letI : Algebra A K := f.toRingHom.toAlgebra
    KaehlerDifferential V A →ₗ[A] K := by
  letI : Algebra A K := f.toRingHom.toAlgebra
  letI : IsScalarTower V A K := IsScalarTower.of_algHom f
  exact (derivation V A K f L hL).liftKaehlerDifferential

theorem cotangentMap_D (a : A) :
    letI : Algebra A K := f.toRingHom.toAlgebra
    cotangentMap V A K f L hL (KaehlerDifferential.D V A a)=(L a).snd := by
  letI : Algebra A K := f.toRingHom.toAlgebra
  letI : IsScalarTower V A K := IsScalarTower.of_algHom f
  exact Derivation.liftKaehlerDifferential_comp_D (derivation V A K f L hL) a
end FieldPoint

section IntegralPoint
variable (f : A →ₐ[V] V)

@[expose] def fieldPoint : A →ₐ[V] K := (Algebra.ofId V K).comp f

variable (L : A →ₐ[V] TrivSqZeroExt K K)
  (hL : ∀ a,(L a).fst=fieldPoint V A K f a)

/-- Genuine integral cotangent pullback evaluated in the same original K.
The balance relation uses the fixed actual integral point A→V and its
composite A→V→K. No hidden-f instance is globally registered. -/
@[expose] def integralFiberMap :
    letI : Algebra A V := f.toRingHom.toAlgebra
    V ⊗[A] KaehlerDifferential V A →ₗ[V] K := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  letI : Algebra A K := (fieldPoint V A K f).toRingHom.toAlgebra
  letI : IsScalarTower V A V := IsScalarTower.of_algHom f
  letI : IsScalarTower V A K := IsScalarTower.of_algHom (fieldPoint V A K f)
  letI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul V (KaehlerDifferential V A →ₗ[A] K)).flip
      (cotangentMap V A K (fieldPoint V A K f) L hL))

theorem integralFiberMap_tmul (v : V) (ω : KaehlerDifferential V A) :
    letI : Algebra A V := f.toRingHom.toAlgebra
    letI : Algebra A K := (fieldPoint V A K f).toRingHom.toAlgebra
    integralFiberMap V A K f L hL (v ⊗ₜ[A] ω)=
      algebraMap V K v*cotangentMap V A K (fieldPoint V A K f) L hL ω := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  letI : Algebra A K := (fieldPoint V A K f).toRingHom.toAlgebra
  letI : IsScalarTower V A V := IsScalarTower.of_algHom f
  letI : IsScalarTower V A K := IsScalarTower.of_algHom (fieldPoint V A K f)
  letI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change v • cotangentMap V A K (fieldPoint V A K f) L hL ω=_
  exact Algebra.smul_def v _

theorem integralFiberMap_differential (a : A) :
    letI : Algebra A V := f.toRingHom.toAlgebra
    integralFiberMap V A K f L hL ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A a)=(L a).snd := by
  letI : Algebra A V := f.toRingHom.toAlgebra
  letI : Algebra A K := (fieldPoint V A K f).toRingHom.toAlgebra
  letI : IsScalarTower V A V := IsScalarTower.of_algHom f
  letI : IsScalarTower V A K := IsScalarTower.of_algHom (fieldPoint V A K f)
  letI : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [integralFiberMap_tmul,map_one,one_mul,cotangentMap_D]
end IntegralPoint
end FirstOrderCotangentEvaluation318
