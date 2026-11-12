module
public import ActualOriginalCompleteGaussProduct318
public import Mathlib.Algebra.Ring.Units
public section
noncomputable section
namespace ActualOriginalCompleteSumBound318
open QuadricCRTAssembly318 ActualOriginalCompleteGaussProduct318 ActualOriginalRationalPoisson318
open ActualOriginalQuadraticGauss318 ActualOriginalUnitGaussBound318
set_option maxHeartbeats 16000000

/-- The actual five-dimensional complete rational-arc coefficient has
uniform squared norm at most32*kappa*q^5 for every unit numerator and full
integer dual frequency. Even and bad-prime moduli require no exceptions. -/
theorem actual_complete_arc_square_bound (κ : ℕ) (hκ : 0 < κ)
    (q : ℕ) [NeZero q] (a : ℤ) (ha : IsUnit (a : ZMod q)) (m : Coordinates ℤ) :
    ‖completeArcCoefficient (κ : ℤ) q a m‖^2 ≤ 32*(κ : ℝ)*(q : ℝ)^5 := by
  have h1 := actual_unit_gauss_one_bound q (a : ZMod q) (m.1.1 : ZMod q) ha
  have h2 := actual_unit_gauss_one_bound q (a : ZMod q) (m.1.2 : ZMod q) ha
  have h3 := actual_unit_gauss_one_bound q (-(a : ZMod q)) (m.2.1.1 : ZMod q) ha.neg
  have h4 := actual_unit_gauss_one_bound q (-(a : ZMod q)) (m.2.1.2 : ZMod q) ha.neg
  have h5 : ‖quadraticGauss q (-(κ : ZMod q)*(a : ZMod q)) (m.2.2 : ZMod q)‖^2 ≤
      (q : ℝ)*(2*(κ : ℝ)) := by
    have he : -(κ : ZMod q)*(a : ZMod q) = (-(a : ZMod q))*(κ : ZMod q) := by ring
    rw [he]
    exact actual_unit_gauss_square_bound q κ hκ (-(a : ZMod q)) (m.2.2 : ZMod q) ha.neg
  rw [actual_complete_arc_gauss_product]
  simp only [Int.cast_natCast]
  calc
    _ = (‖quadraticGauss q (a : ZMod q) (m.1.1 : ZMod q)‖^2 *
          ‖quadraticGauss q (a : ZMod q) (m.1.2 : ZMod q)‖^2) *
        ((‖quadraticGauss q (-(a : ZMod q)) (m.2.1.1 : ZMod q)‖^2 *
          ‖quadraticGauss q (-(a : ZMod q)) (m.2.1.2 : ZMod q)‖^2) *
          ‖quadraticGauss q (-(κ : ZMod q)*(a : ZMod q)) (m.2.2 : ZMod q)‖^2) := by
      simp only [norm_mul]
      ring
    _ ≤ ((2*(q : ℝ))*(2*(q : ℝ))) *
        (((2*(q : ℝ))*(2*(q : ℝ))) * ((q : ℝ)*(2*(κ : ℝ)))) := by
      gcongr <;> assumption
    _ = _ := by ring

theorem actual318_complete_arc_square_bound (q : ℕ) [NeZero q] (a : ℤ)
    (ha : IsUnit (a : ZMod q)) (m : Coordinates ℤ) :
    ‖completeArcCoefficient 318 q a m‖^2 ≤ 10176*(q : ℝ)^5 := by
  have h := actual_complete_arc_square_bound 318 (by omega) q a ha m
  norm_num at h
  exact h

theorem actual326_complete_arc_square_bound (q : ℕ) [NeZero q] (a : ℤ)
    (ha : IsUnit (a : ZMod q)) (m : Coordinates ℤ) :
    ‖completeArcCoefficient 326 q a m‖^2 ≤ 10432*(q : ℝ)^5 := by
  have h := actual_complete_arc_square_bound 326 (by omega) q a ha m
  norm_num at h
  exact h

end ActualOriginalCompleteSumBound318
