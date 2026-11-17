module
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section
namespace DualNumberCotangentCertificate318

variable {A K : Type*} [CommRing A] [Field K]
variable (point : A →+* K) (lift : Fin 3 → A →+* DualNumber K)
variable (lift_fst : ∀ j x, (lift j x).fst = point x)

/-- Every first-order lift of a point kills the square of its kernel.
This is an ideal-level statement, with no smoothness assumption. -/
theorem lift_kills_square (j : Fin 3) {x : A}
    (hx : x ∈ (RingHom.ker point) ^ 2) : lift j x = 0 := by
  have hle : (RingHom.ker point) ^ 2 ≤ RingHom.ker (lift j) := by
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change lift j (a * b) = 0
    rw [map_mul]
    have ha' : point a = 0 := RingHom.mem_ker.mp ha
    have hb' : point b = 0 := RingHom.mem_ker.mp hb
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mul, lift_fst, ha', hb', zero_mul,
        TrivSqZeroExt.fst_zero]
    · simp only [DualNumber.snd_mul, lift_fst, ha', hb', zero_mul, mul_zero,
        zero_add, TrivSqZeroExt.snd_zero]
  exact RingHom.mem_ker.mp (hle hx)

variable (root : Fin 3 → A)
variable (lift_root : ∀ j i, lift j (root i) =
  TrivSqZeroExt.inr (if i = j then (1 : K) else 0))

theorem root_mem_kernel (i : Fin 3) : root i ∈ RingHom.ker point := by
  rw [RingHom.mem_ker, ← lift_fst 0 (root i), lift_root]
  rfl

/-- A concrete certificate of linear independence of three cotangent
classes: any relation modulo the square of the point ideal has every
coefficient zero in the residue field. Coefficients range over ALL A. -/
theorem independent_mod_square (a : Fin 3 → A)
    (ha : (∑ i, a i * root i) ∈ (RingHom.ker point) ^ 2) :
    ∀ j, point (a j) = 0 := by
  intro j
  have h := congrArg TrivSqZeroExt.snd
    (lift_kills_square point lift lift_fst j ha)
  simpa [map_sum, map_mul, TrivSqZeroExt.snd_sum, DualNumber.snd_mul,
    lift_root, lift_fst] using h

end DualNumberCotangentCertificate318
