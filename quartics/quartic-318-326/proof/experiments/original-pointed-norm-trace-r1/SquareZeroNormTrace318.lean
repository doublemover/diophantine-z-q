module
public import OriginalFivePointedClassification318
public import Mathlib.RingTheory.NormTrace
public section
noncomputable section
namespace SquareZeroNormTrace318
set_option maxHeartbeats 1300000
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (e : A) (he : e * e = 0)
include he in
/-- The determinant norm on an ACTUAL finite-free algebra over an arbitrary
possibly nonreduced ring has the original trace as its square-zero coefficient. -/
lemma norm_one_add (x : B) : Algebra.norm A (1 + algebraMap A B e * x) =
    1 + e * Algebra.trace A B x := by
  obtain ⟨q,hq⟩ := Algebra.norm_one_add_smul e x
  have he' : e ^ 2 = 0 := by simpa only [pow_two] using he
  rw [Algebra.smul_def, he', mul_zero, add_zero, mul_comm (Algebra.trace A B x) e] at hq
  exact hq
include he in
lemma epsilon_square : algebraMap A B e * algebraMap A B e = 0 := by
  rw [← map_mul, he, map_zero]
/-- The genuine unit norm, not only a ring-level first-order label. -/
lemma norm_infinitesimal (x : B) :
    Units.map (Algebra.norm A)
      (InfinitesimalUnitCocycle318.infinitesimal (algebraMap A B e) (epsilon_square e he) x) =
    InfinitesimalUnitCocycle318.infinitesimal e he (Algebra.trace A B x) := by
  apply Units.ext
  exact norm_one_add e he x
end SquareZeroNormTrace318
