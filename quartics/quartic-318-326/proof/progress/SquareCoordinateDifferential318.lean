module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace SquareCoordinateDifferential318
set_option maxHeartbeats 200000
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Exact universal derivative of a ramified square-coordinate equation. -/
theorem D_of_square (t z : S) (a k : R)
    (h : t-algebraMap R S a=algebraMap R S k*z^2) :
    KaehlerDifferential.D R S t = (2*algebraMap R S k*z) • KaehlerDifferential.D R S z := by
  have hd := congrArg (KaehlerDifferential.D R S) h
  simp only [pow_two,map_sub,Derivation.map_algebraMap,sub_zero,
    Derivation.leibniz,smul_zero,add_zero] at hd
  calc
    KaehlerDifferential.D R S t = algebraMap R S k •
        (z • KaehlerDifferential.D R S z + z • KaehlerDifferential.D R S z) := hd
    _ = (2*algebraMap R S k*z) • KaehlerDifferential.D R S z := by
      simp only [smul_smul,←add_smul]
      congr 1
      ring

theorem frame_D_of_square (e : KaehlerDifferential R S ≃ₗ[S] S)
    (t z : S) (a k : R) (h : t-algebraMap R S a=algebraMap R S k*z^2)
    (hz : e (KaehlerDifferential.D R S z)=1) :
    e (KaehlerDifferential.D R S t)=2*algebraMap R S k*z := by
  rw [D_of_square t z a k h,map_smul,hz]
  exact mul_one _
end SquareCoordinateDifferential318
