module
public import IntrinsicTensorFrameValue318
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public section
noncomputable section
namespace FramedCotangentFiber318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K]
/-- The actual affine relative cotangent fiber. This is scalar extension of
Omega(A/R), not Omega(K/R), which would lose the geometric tangent direction. -/
abbrev Fiber := K ⊗[A] KaehlerDifferential R A
@[expose] def frame (e : KaehlerDifferential R A ≃ₗ[A] A) : Fiber R A K ≃ₗ[K] K :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid A K K

@[expose] def differential (a : A) : Fiber R A K :=
  (1:K) ⊗ₜ[A] KaehlerDifferential.D R A a

theorem frame_tmul (e : KaehlerDifferential R A ≃ₗ[A] A) (k : K) (ω : KaehlerDifferential R A) :
    frame R A K e (k ⊗ₜ[A] ω)=algebraMap A K (e ω)*k := by
  simp only [frame,LinearEquiv.trans_apply,TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply,TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def]

theorem frame_differential (e : KaehlerDifferential R A ≃ₗ[A] A) (a : A) :
    frame R A K e (differential R A K a)=algebraMap A K (e (KaehlerDifferential.D R A a)) := by
  rw [differential,frame_tmul,mul_one]

abbrev Square := Fiber R A K ⊗[K] Fiber R A K
@[expose] def squareFrame (e : KaehlerDifferential R A ≃ₗ[A] A) : Square R A K ≃ₗ[K] K :=
  TensorProduct.congr (frame R A K e) (frame R A K e) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid K K K

theorem squareFrame_tmul (e : KaehlerDifferential R A ≃ₗ[A] A) (ω η : Fiber R A K) :
    squareFrame R A K e (ω ⊗ₜ[K] η)=frame R A K e ω*frame R A K e η := by
  simp only [squareFrame,LinearEquiv.trans_apply,TensorProduct.congr_tmul,
    TensorProduct.AlgebraTensorModule.rid_tmul,smul_eq_mul]
  exact mul_comm _ _

/-- The fiber of an actual coefficient times a coordinate differential square. -/
@[expose] def weighted (a s : A) : Square R A K :=
  algebraMap A K a • (differential R A K s ⊗ₜ[K] differential R A K s)

theorem weighted_value (e : KaehlerDifferential R A ≃ₗ[A] A) (a s : A)
    (hs : e (KaehlerDifferential.D R A s)=1) :
    squareFrame R A K e (weighted R A K a s)=algebraMap A K a := by
  rw [weighted,map_smul,squareFrame_tmul,frame_differential,hs,map_one,one_mul,smul_eq_mul,mul_one]
end FramedCotangentFiber318
