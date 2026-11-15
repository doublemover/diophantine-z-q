module
public import FramedCotangentFiber318
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public section
noncomputable section
namespace EtaleEvaluatedCotangent318
open scoped TensorProduct
set_option maxHeartbeats 800000
variable (R A C K : Type*) [CommRing R] [CommRing A] [CommRing C] [Field K]
  [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
  [Algebra A K] [Algebra C K] [IsScalarTower A C K]
  [Algebra.FormallyEtale A C]

/-- Canonical change of actual affine neighborhood at a fixed evaluated
point: tensor cancellation followed by the true etale Kahler isomorphism.
It is NOT the differential module of the field K itself. -/
@[expose] def transport :
    K ⊗[A] KaehlerDifferential R A ≃ₗ[K] K ⊗[C] KaehlerDifferential R C :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange A C K K
    (KaehlerDifferential R A)).symm ≪≫ₗ
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A C)

/-- The canonical map retains the actual universal differential of
EVERY source element, not just a generator or its scalar span. -/
theorem transport_differential (a : A) :
    transport R A C K ((1:K) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      (1:K) ⊗ₜ[C] KaehlerDifferential.D R C (algebraMap A C a) := by
  simp only [transport,LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]

variable (B : Type*) [CommRing B] [Algebra R B] [Algebra B C]
  [IsScalarTower R B C] [Algebra B K] [IsScalarTower B C K]
  [Algebra.FormallyEtale B C]

/-- Actual comparison between two charts through their constructed
common affine neighborhood, with its specified common point evaluation. -/
@[expose] def comparison :
    K ⊗[A] KaehlerDifferential R A ≃ₗ[K] K ⊗[B] KaehlerDifferential R B :=
  transport R A C K ≪≫ₗ (transport R B C K).symm

/-- Equality of the actual functions on the common chart gives equality
of their actual cotangent vectors under the canonical comparison. -/
theorem comparison_differential (a : A) (b : B)
    (h : algebraMap A C a = algebraMap B C b) :
    comparison R A C K B ((1:K) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      (1:K) ⊗ₜ[B] KaehlerDifferential.D R B b := by
  apply (transport R B C K).injective
  simp only [comparison,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    transport_differential,h]

/-- A frame constructed on the second chart gives a frame on the
actual evaluated first-chart fiber, without requiring a frame there. -/
@[expose] def frame (e : KaehlerDifferential R B ≃ₗ[B] B) :
    K ⊗[A] KaehlerDifferential R A ≃ₗ[K] K :=
  comparison R A C K B ≪≫ₗ FramedCotangentFiber318.frame R B K e

theorem frame_shared_differential (e : KaehlerDifferential R B ≃ₗ[B] B)
    (a : A) (b : B) (h : algebraMap A C a = algebraMap B C b) :
    frame R A C K B e ((1:K) ⊗ₜ[A] KaehlerDifferential.D R A a) =
      algebraMap B K (e (KaehlerDifferential.D R B b)) := by
  rw [frame,LinearEquiv.trans_apply,comparison_differential R A C K B a b h]
  exact FramedCotangentFiber318.frame_differential R B K e b
end EtaleEvaluatedCotangent318
