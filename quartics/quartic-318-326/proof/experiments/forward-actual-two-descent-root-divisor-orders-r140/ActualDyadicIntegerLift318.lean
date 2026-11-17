module
public import ActualOddBadLocalDensity318
public section
noncomputable section
namespace ActualDyadicIntegerLift318
open QuadricCRTAssembly318 ActualQuadricTaylor318 ActualOriginalModularLift318
set_option maxHeartbeats 26000000

lemma original_derivative_even (κ : ℤ) (x h : Coordinates ℤ) : 2∣derivative κ x h := by
  refine ⟨x.1.1*h.1.1+x.1.2*h.1.2-x.2.1.1*h.2.1.1-x.2.1.2*h.2.1.2-κ*x.2.2*h.2.2,?_⟩
  unfold derivative
  ring

/-- In contrast to odd-prime Hensel lifting, at an even modulus every
one of the 32 top digits has the SAME next-level quadratic test. -/
theorem actual_even_translate_congruence (κ m : ℤ) (hm : 2∣m) (x h : Coordinates ℤ) :
    (2*m)∣equation κ (translate x h m)-equation κ x := by
  obtain ⟨u,hu⟩ := hm
  obtain ⟨v,hv⟩ := original_derivative_even κ x h
  refine ⟨v+u*equation κ h,?_⟩
  rw [original_taylor,hv,hu]
  ring

theorem actual_even_lift_iff (κ m : ℤ) (hm : 2∣m) (x h : Coordinates ℤ) :
    (2*m)∣equation κ (translate x h m) ↔ (2*m)∣equation κ x := by
  have hh := actual_even_translate_congruence κ m hm x h
  constructor
  · intro ht
    have hd := dvd_sub ht hh
    simpa only [sub_sub_cancel] using hd
  · intro hx
    have hd := dvd_add hh hx
    simpa only [sub_add_cancel] using hd

/-- The whole dyadic digit fiber is therefore either ALL five-bit
tuples or empty. A false p^4-per-base Hensel count is not used at2. -/
theorem actual_dyadic_digit_test (κ m : ℤ) (hm : 2∣m) (x : Coordinates ℤ)
    (h : Coordinates (ZMod 2)) :
    (2*m)∣equation κ (translate x (digits 2 h) m) ↔ (2*m)∣equation κ x :=
  actual_even_lift_iff κ m hm x (digits 2 h)

end ActualDyadicIntegerLift318
