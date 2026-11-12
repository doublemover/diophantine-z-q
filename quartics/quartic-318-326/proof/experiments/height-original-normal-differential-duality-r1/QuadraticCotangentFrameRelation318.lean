module
public import FramedCotangentFiber318
public section
noncomputable section
namespace QuadraticCotangentFrameRelation318
open KaehlerDifferential
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Differentiate the actual quadratic equation in Omega(A/R), then
apply the constructed dt frame. No division by the root is performed. -/
theorem relation (e : KaehlerDifferential R A ≃ₗ[A] A)
    (t z : A) (a d : R) (ht : e (D R A t) = 1)
    (hz : z^2 = algebraMap R A d * (t - algebraMap R A a)) :
    2*z*e (D R A z) = algebraMap R A d := by
  have h := congrArg (fun x => e (D R A x)) hz
  rw [pow_two] at h
  simp only [Derivation.leibniz, map_add, map_sub, Derivation.map_algebraMap,
    map_smul, map_zero, smul_zero, add_zero, sub_zero, smul_eq_mul, ht, mul_one] at h
  calc
    2*z*e (D R A z) = z*e (D R A z)+z*e (D R A z) := by ring
    _ = algebraMap R A d := h

variable (K : Type*) [Field K] [Algebra A K]
/-- The same undivided relation in the genuine cotangent fiber at the
specified ring point, not in Omega(K/R). -/
theorem fiber_relation (e : KaehlerDifferential R A ≃ₗ[A] A)
    (t z : A) (a d : R) (ht : e (D R A t) = 1)
    (hz : z^2 = algebraMap R A d * (t - algebraMap R A a)) :
    2 * algebraMap A K z * FramedCotangentFiber318.frame R A K e
      (FramedCotangentFiber318.differential R A K z) =
        algebraMap A K (algebraMap R A d) := by
  rw [FramedCotangentFiber318.frame_differential]
  simpa only [map_mul,map_ofNat] using congrArg (algebraMap A K)
    (relation e t z a d ht hz)
end QuadraticCotangentFrameRelation318
