module
public import FractionKaehlerFrame318
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public section
noncomputable section
namespace IntegralCotangentTensor318
open scoped TensorProduct
set_option maxHeartbeats 400000

/-- The tensor-square frame of an actual rank-one module. -/
@[expose] def squareFrame {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (e : M ≃ₗ[A] A) : (M ⊗[A] M) ≃ₗ[A] A :=
  (TensorProduct.congr e e).trans (TensorProduct.lid A A)

theorem squareFrame_pure {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (e : M ≃ₗ[A] A) (x y : M) : squareFrame e (x ⊗ₜ[A] y) = e x * e y := by
  rfl

variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B] [Field K]
  [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K] [IsFractionRing B K]
  (e : KaehlerDifferential R B ≃ₗ[B] B)

/-- The map of cotangent tensor squares to the fraction field, expressed in
actual frames. `map_pure` identifies it with the original differential map
on both tensor factors, so this is not a separately chosen scalar lattice. -/
@[expose] def map :
    (KaehlerDifferential R B ⊗[B] KaehlerDifferential R B) →ₗ[B]
      (KaehlerDifferential R K ⊗[K] KaehlerDifferential R K) :=
  ((squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e)).symm.toLinearMap.restrictScalars B).comp
    ((Algebra.linearMap B K).comp (squareFrame e).toLinearMap)

theorem frame_map (x : KaehlerDifferential R B ⊗[B] KaehlerDifferential R B) :
    squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e) (map e x) =
      algebraMap B K (squareFrame e x) := by
  exact (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e)).apply_symm_apply _

theorem map_pure (x y : KaehlerDifferential R B) :
    map (K := K) e (x ⊗ₜ[B] y) =
      (KaehlerDifferential.map R R B K x) ⊗ₜ[K] (KaehlerDifferential.map R R B K y) := by
  apply (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e)).injective
  rw [frame_map, squareFrame_pure, squareFrame_pure,
    FractionKaehlerFrame318.genericFrame_map, FractionKaehlerFrame318.genericFrame_map, map_mul]

/-- Changing the integral frame does not change the tensor map. -/
theorem map_independent (f : KaehlerDifferential R B ≃ₗ[B] B) :
    map (K := K) e = map f := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rw [map_pure, map_pure]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_injective : Function.Injective (map (K := K) e) := by
  intro x y h
  apply (squareFrame e).injective
  apply IsFractionRing.injective B K
  simpa only [frame_map] using congrArg
    (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e)) h

/-- Exact lattice criterion for an actual generic quadratic differential. -/
theorem integral_iff (q : KaehlerDifferential R K ⊗[K] KaehlerDifferential R K) :
    (∃ x, map e x = q) ↔ ∃ b : B, algebraMap B K b =
      squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e) q := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨squareFrame e x, (frame_map e x).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨(squareFrame e).symm b, ?_⟩
    apply (squareFrame (FractionKaehlerFrame318.genericFrame (K := K) e)).injective
    rw [frame_map, LinearEquiv.apply_symm_apply, hb]

end IntegralCotangentTensor318
