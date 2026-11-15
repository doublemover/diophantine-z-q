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
local instance pointAction : Algebra A K := f.toRingHom.toAlgebra
local instance pointTower : IsScalarTower V A K := IsScalarTower.of_algHom f

/-- Extract the derivative of the CONSTRUCTED first-order lift. The module
A-action on K is exactly its projected original point f. -/
@[expose] def derivation : Derivation V A K where
  toLinearMap := ((TrivSqZeroExt.sndHom K K).restrictScalars V).comp L.toLinearMap
  map_one_eq_zero' := by
    change (L 1).snd=0
    rw [map_one]
    rfl
  leibniz' a b := by
    change (L (a*b)).snd=f a*(L b).snd+f b*(L a).snd
    rw [map_mul,TrivSqZeroExt.snd_mul]
    change (L a).fst*(L b).snd+(L a).snd*(L b).fst=f a*(L b).snd+f b*(L a).snd
    rw [hL a,hL b]
    ring

/-- The native universal differential map, with no assumed derivation or
free cotangent frame. -/
@[expose] def cotangentMap : KaehlerDifferential V A →ₗ[A] K :=
  (derivation V A K f L hL).liftKaehlerDifferential

theorem cotangentMap_D (a : A) :
    cotangentMap V A K f L hL (KaehlerDifferential.D V A a)=(L a).snd :=
  Derivation.liftKaehlerDifferential_comp_D (derivation V A K f L hL) a
end FieldPoint

section IntegralPoint
variable (f : A →ₐ[V] V)

@[expose] def fieldPoint : A →ₐ[V] K := (Algebra.ofId V K).comp f

local instance integralAction : Algebra A V := f.toRingHom.toAlgebra
local instance fieldAction : Algebra A K := (fieldPoint V A K f).toRingHom.toAlgebra
local instance integralTower : IsScalarTower V A V := IsScalarTower.of_algHom f
local instance fieldTower : IsScalarTower V A K := IsScalarTower.of_algHom (fieldPoint V A K f)
local instance evaluationTower : IsScalarTower A V K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (L : A →ₐ[V] TrivSqZeroExt K K)
  (hL : ∀ a,(L a).fst=fieldPoint V A K f a)

/-- Genuine integral cotangent pullback evaluated in the same original K.
The balance relation uses the actual integral point A→V and its composite
A→V→K, not an independently chosen A-action. -/
@[expose] def integralFiberMap : V ⊗[A] KaehlerDifferential V A →ₗ[V] K :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul V (KaehlerDifferential V A →ₗ[A] K)).flip
      (cotangentMap V A K (fieldPoint V A K f) L hL))

theorem integralFiberMap_tmul (v : V) (ω : KaehlerDifferential V A) :
    integralFiberMap V A K f L hL (v ⊗ₜ[A] ω)=
      algebraMap V K v*cotangentMap V A K (fieldPoint V A K f) L hL ω := by
  change v • cotangentMap V A K (fieldPoint V A K f) L hL ω=_
  exact Algebra.smul_def v _

theorem integralFiberMap_differential (a : A) :
    integralFiberMap V A K f L hL ((1:V) ⊗ₜ[A] KaehlerDifferential.D V A a)=(L a).snd := by
  rw [integralFiberMap_tmul,map_one,one_mul,cotangentMap_D]
end IntegralPoint
end FirstOrderCotangentEvaluation318
