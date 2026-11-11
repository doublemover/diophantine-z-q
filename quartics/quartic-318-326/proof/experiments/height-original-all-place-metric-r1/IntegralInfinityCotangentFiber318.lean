module
public import OriginalFiniteCotangentCenters318
public section
noncomputable section
namespace IntegralInfinityCotangentFiber318
open scoped TensorProduct
open IntegralInfinityChart318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (h2 : IsUnit (2:R))
  (K : Type*) [Field K] (φ : Order R c →+* K)
local instance evaluationAlgebra : Algebra (Order R c) K := φ.toAlgebra
abbrev Fiber := FramedCotangentFiber318.Fiber R (Order R c) K
@[expose] def frame : Fiber R c K φ ≃ₗ[K] K :=
  FramedCotangentFiber318.frame R (Order R c) K (IntegralInfinityChart318.frame R c h2)
@[expose] def du : Fiber R c K φ :=
  FramedCotangentFiber318.differential R (Order R c) K (coordinate R c)

theorem du_value : frame R c h2 K φ (du R c K φ)=1 := by
  rw [frame,du,FramedCotangentFiber318.frame_differential,IntegralInfinityChart318.frame_D,map_one]

/-- The parameter differential in the infinity fiber, using the coefficient
supplied by the actual whole-overlap differential identity below. -/
@[expose] def parameter (d : K) : Fiber R c K φ := d • du R c K φ

theorem parameter_value (d : K) : frame R c h2 K φ (parameter R c K φ d)=d := by
  rw [parameter,map_smul,du_value,smul_eq_mul,mul_one]

@[expose] def section (n : Fin 2) : FramedCotangentFiber318.Square R (Order R c) K :=
  FramedCotangentFiber318.weighted R (Order R c) K
    (IntegralGlobalBicanonicalPair318.infinityCoefficient R c n) (coordinate R c)

theorem section_value (n : Fin 2) :
    FramedCotangentFiber318.squareFrame R (Order R c) K (IntegralInfinityChart318.frame R c h2)
      (section R c K φ n)=φ (IntegralGlobalBicanonicalPair318.infinityCoefficient R c n) :=
  FramedCotangentFiber318.weighted_value _ _ _ _ _ _ (IntegralInfinityChart318.frame_D R c h2)
end IntegralInfinityCotangentFiber318
